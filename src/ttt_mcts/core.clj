(ns ttt-mcts.core
  (:gen-class))

  (comment
    This program implements a monte carlo search algorithm to play tic-tac-toe.
  )
    ;The "MCTS" algorithm has four steps
    ;1) Randomly pick a branch of the tree (in practice, the more
    ;  successful branches are usually weighted to be chosen more).
    ;2) Expand the branch (create a node).
    ;3) Simulate or play the game (from the new node) until termination.
    ;4) Propogate the result back up the tree.
    
    ;Once the computational budget is used up, the branch with
    ;the highest winning % is chosen as the next move.
    
    ;MCTS has been the most successful tree search algorithm for computer go.
    
 
    ;Nick Brandaleone - July 2015
 
    ;See website for more info. http://mcts.ai
    ;See https://sites.google.com/a/lclark.edu/drake/courses/drakepedia/monte-carlo-tree-search.
    
    ;Code based upon http://mcts.ai/code/java.html, and 
    ;http://randomcomputation.blogspot.com/2013/01/monte-carlo-tree-search-in-clojure.html
 
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;; Set-up board and parse moves
  ;;
 
  ;; The players are :X and :O, empty spots are "0"s.
  ;; The board state is represented by vector. For example: [0 :X :X :O :O :X 0 0 0]
  ;; Computational budget is how many games to play until termination.
  
  ;; The UCT game database is represented by "mem" hash map. 
  ;; Every state has the following data:
  (comment
    {[0 0 0 0 0 0 0 0 0] 
      {:visits 0, :draws 0, :x-win 0, :o-win 0, :chldn ([0 0 0 0 0 0 0 0 :X] 
        [0 0 0 0 0 0 0 :X 0],..., [:X 0 0 0 0 0 0 0 0]), :to-move :X}})
        
  
  (def wins
    [[0 1 2] [3 4 5] [6 7 8]  ; cols
     [0 3 6] [1 4 7] [2 4 8]  ; rows
     [0 4 8] [2 4 6]])        ; diagonals
 
  ; keep track of whose turn it is. nil returns :X
  (defn opp-player [p] (if (= p :X) :O :X))
  
  ; The number 0 is a blank
  (defn blank? [x] (number? x))
  
  (defn win-check [state player]
    (loop [wins wins]
      (if (empty? wins) false
        (let [[a b c] (first wins)]
        ;(println (str a b c))
          (if (and (= player (get state a))
                   (= player (get state b))
                   (= player (get state c)))
            true
            (recur (rest wins)))))))
    
  ; returns win/lose/draw map. False if game not finished.
  (defn ttt-terminal? [state]
    (if (win-check state :X)      {:draws 0 :x-win 1 :o-win 0}
      (if (win-check state :O)    {:draws 0 :x-win 0 :o-win 1}
      (if (not-any? blank? state) {:draws 1 :x-win 0 :o-win 0} false))))
  ; (ttt-terminal? [0 0 :O :O 0 :X :X :X :X])
  ; {:draws 0, :x-win 1, :o-win 0}
      
  ; creates new children nodes from current board state and 
  ; associates new branch
  ;; Added default to-move :X, in case passed nil. 
  (defn ttt-gen-children [state & [to-move]]
    (let [to-move (or to-move :X)]
    (for [[i v] (zipmap (range) state)
      :when (blank? v)]
      (assoc state i to-move))))
  ;(ttt-gen-children [0 0 :O :O 0 :X :X 0 0] :X)
  ;([0 0 :O :O 0 :X :X 0 :X] ... [0 :X :O :O 0 :X :X 0 0] [:X 0 :O :O 0 :X :X 0 0])
  
  ; Playouts are the game simulation.
  ; Returns the result of picking a single game tree path randomly.
  ; It is possible that running the same playout twice will give win and then loss
  ; as the moves are chosen randomly.
  (defn ttt-playout
    "Returns a value of playout simulation for tic tac toe"
    [state to-move]
    (loop [state state to-move to-move]
      (if-let [result (ttt-terminal? state)] result
        (recur (rand-nth (ttt-gen-children state to-move))
          (opp-player to-move)))))
  ;(ttt-playout [0 0 :O :O 0 :X :X :X 0] :O)
  ;{:draws 0, :x-win 1, :o-win 0}
  ;(ttt-playout [0 0 :O :O 0 :X :X :X 0] :O)
  ; {:draws 0, :x-win 0, :o-win 1}
      
  ;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;  UCT (Upper Confidence bound, applied to Trees) code
  ;;  UCT is the name of the MCTS algorithm
  ;;
  
  (def init-record
    "The data associated with a board-state in the mem"
    {:visits 0, :draws 0
      :x-win 0, :o-win 0
      :chldn [], :to-move :X}) ; X moves first
      
  (def init-mem
    "Creates initial mem for TTT"
    (let [init-state [0 0 0 0 0 0 0 0 0]]
      {init-state
        (assoc init-record :chldn (ttt-gen-children init-state :X))}))
        
  (defn uct-value
    "Value of a state based on gathered statistics"
    ; Currently not true to UCT value as published.
    [{:keys [visits x-win o-win draws to-move]}]
    (case (opp-player to-move)
    :X (/ (+ x-win (/ draws 2)) ; win = 1 point, draw = 1/2 point
          visits)
    :O (/ (+ o-win (/ draws 2))
          visits)
    :default 0))
    
  (defn uct-sample
    "The random sampling function for a board state"
    ; the supplied func is always playout. times is typically 1.
    ; Plays a random game from starting node, and returns result.
    [state mem func times]
    (loop [result {:draws 0 :x-win 0 :o-win 0} times times]
      (if (< times 1) result
         (recur (reduce
                  (fn [m [k v]]            ; destructures the map into key/value
                    (update-in m [k] + v)) ; update wins/draws for playout
                    result
                    (func state (get-in mem [state :to-move])))
                (dec times)))))
                
  ; This is the selection that is done after the computational budget
  ; is used up. We select the move with the highest winning %                  
  (defn uct-select
    "Selects highest rated child of state"
    [mem state]
    (let [chldn (get-in mem [state :chldn])
      explored (remove #(zero? (get-in mem [% :visits] 0)) chldn)]
      (if (empty? explored)
        (rand-nth chldn)
        (apply max-key #(uct-value (get mem %)) explored))))
  
  ; When visits = 0, create children branches of node 
  ; BUG? When state is new, :to-move will not exist.     
  (defn uct-unexplored [mem state]
    "Unexplored children of state"
    (for [c (get-in mem [state :chldn]
        (ttt-gen-children state (get-in mem [state :to-move])))
      :when (zero? (get-in mem [c :visits] 0))] c))
      
  ; Pass the game result back up the "tree"
  (defn uct-backprop
    "Backpropogates child value to the parent"
    [mem path {:keys [x-win o-win draws] :as stats}]
    (if (empty? path) mem
      (recur 
        (-> mem   ; thread-first macro
          (update-in [(first path) :x-win] + x-win)
          (update-in [(first path) :o-win] + o-win)
          (update-in [(first path) :draws] + draws)
          (update-in [(first path) :visits] inc))
        (rest path)
          stats)))
   
  (defn- add-child
    "Helper function to create child-record for the mem"
    [mem parent-state child-state]
    (let [to-move (get-in mem [parent-state :to-move])
        child-record (get mem child-state
                    (assoc init-record
                      :chldn (ttt-gen-children child-state (opp-player to-move))
                      :to-move (opp-player to-move)))]
        (assoc mem child-state child-record)))   
  
  (defn uct-grow
    "Estimates a child's value and adds it to the tree"
    [mem path]
    (let [leaf (first path)
      chld (rand-nth (uct-unexplored mem leaf))
      valu (uct-sample chld mem ttt-playout 1)]
      (-> mem
        (add-child leaf chld)
        (uct-backprop (cons chld path) valu))))
 
  (defn learn-iteration [mem state]
    "The core algorithm; a single analysis of a state. Searches the tree
    for an unexplored child, estimates the child's value, adds
    it to the tree, and backpropogates the value up the path."
    (loop [mem mem, state state, path (list state)]
      (if-let [result (ttt-terminal? state)]
        (uct-backprop mem path result)
        (if (not-empty (uct-unexplored mem state))
          (uct-grow mem path)
          (let [ch (uct-select mem state)]
            (recur mem ch (cons ch path)))))))
          
  (defn learn-state [mem state budget]
    "Analyzes a board state using the UCT algorithm. Iterates
    learn-iteration until budget is exhausted."
    (loop [mem mem budget budget]
      (if (< budget 1) mem
        (recur (learn-iteration mem state) (dec budget)))))
        
  ;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;  Run the game
  ;;        
  
  (defn print-board [board]
    "Pretty print a board state"
    (println
      (apply format "%s %s %s \n%s %s %s \n%s %s %s \n"
        (map #(case % :X "X" :O "O" 0 "_") board))))
        
  ; Play against random opponent. Saves memory database between runs.
  (defn play-game
    "Retains memory built from analysis of past moves"
    ;[[mem _]]
    [mem]
    (let [uctp (rand-nth [:X :O])]
      (loop [mem mem
             board-state [0 0 0 0 0 0 0 0 0]
             to-move :X]
        (if-let [{:keys [draws x-win o-win]} (ttt-terminal? board-state)]
          [mem
            (hash-map
              :uct (if (= uctp :X) x-win o-win)
              :rnd (if (= uctp :X) o-win x-win)
              :draws draws)]
            (if (= uctp to-move)
              (let [mem (learn-state mem board-state 30)  ; 30 game budget per move
                  move (uct-select mem board-state)]
                  (recur mem move (opp-player to-move)))
              (let [move (rand-nth (get-in mem [board-state :chldn]))
                    mem (if (contains? mem move) mem
                      (assoc mem move
                          (assoc init-record
                            :chldn (ttt-gen-children
                                      move
                                      (opp-player to-move))
                            :to-move (opp-player to-move))))]
                    (recur mem move (opp-player to-move))))))))
                    
  (defn play-game-no-mem
    "Does not retain memory over moves to allow for
    assessment based on computational budget"
    [budget]
    (let [uctp (rand-nth [:X :O])]
      (loop [board-state [0 0 0 0 0 0 0 0 0]
        to-move :X]
        ; (print-board board-state)     ; DEBUG. See game in action.
        (if-let [{:keys [draws x-win o-win]} (ttt-terminal? board-state)]
          (hash-map
            :uct (if (= uctp :X) x-win o-win)
            :rnd (if (= uctp :X) o-win x-win)
            :draws draws)
          (if (= uctp to-move)
            (let [mem (learn-state (hash-map
                                    board-state
                                    (assoc init-record  ; reset memory every turn
                                      :to-move to-move
                                      :chldn (ttt-gen-children
                                        board-state
                                        to-move)))
                                    board-state
                                    budget)
                    move (uct-select mem board-state)]
                  (recur move (opp-player to-move)))
              (let [move (rand-nth (ttt-gen-children board-state to-move))]
                  (recur move (opp-player to-move))))))))
  
  (defn- update-stats
    "Helper function"
    [curr new]
    (reduce (fn [m [k v]] (update-in m [k] + v))
    curr new))
    
  ; Plays better game every time. 30 games per move budget as default.
  (defn uct-v-rand
    "Plays n games of uct vs rand retaining the analysis memory across games"
    [n]
      (loop [mem init-mem games 0 stats {:uct 0 :rnd 0 :draws 0}]
        (if (>= games n) [mem stats]
          (let [[mem result] (play-game mem)]
            (recur mem
              (inc games)
              (update-stats stats result))))))
             
  ;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;  Test effectiveness of MCTS
  ;;  
  
  (defn get-stats []
    "generate statistics of a random player vs. MCTS, with different
    budgets. No memory is saved across runs."
    (let [data (for [b [0 1 2 3 4 5 10 100]]  ; computational budget
            (list b (take 50 (repeatedly #(play-game-no-mem b))))) ; play 50 games per budget
          stats (map (fn [[b d]]
            ; map can be used here "(map :uct d)" as :uct is function lookup
                  (let [avgs {:uct   (float (/ (reduce + (map :uct d)) (count d)))
                              :rnd   (float (/ (reduce + (map :rnd d)) (count d)))
                              :draws (float (/ (reduce + (map :draws d)) (count d)))}]
                    (list b avgs)))
                  data)]
        (println stats))) ; should break this up for 1 line per stat
   
  ;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;  Main
  ;;    
  
  ;; This program is NOT meant for player vs computer tic-tac-toe.
  ;; It is for testing the effectiveness of MCTS algorithm.
  ;; The three main functions are:
  ;;    1) uct-v-rand [n]               ... Plays MCTS vs random player with memory saved
  ;;    2) player-game-no-mem [budget]  ... Plays MCTS vs random player with no memory
  ;;    3) play-game [mem]              ... Used for #1
(defn -main
  "Run the statistics of random player vs. MCTS with varying budget"
  [& args]
  (println "Budget                                    Result")
  (println "================================================")
  (get-stats)
  (println "================================================"))
  
