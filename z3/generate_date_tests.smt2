; DateHelper test case generation script
(set-logic QF_LIA)

; Declare date component variables
(declare-const year Int)
(declare-const month Int)
(declare-const day Int)
(declare-const hour Int)
(declare-const minute Int)
(declare-const second Int)

; Basic constraints - valid date ranges
(assert (>= year 1970)) ; Unix epoch start
(assert (<= year 2100)) ; Reasonable future limit
(assert (>= month 1))
(assert (<= month 12))
(assert (>= day 1))
(assert (<= day 31)) ; More precise constraints needed per month
(assert (>= hour 0))
(assert (<= hour 23))
(assert (>= minute 0))
(assert (<= minute 59))
(assert (>= second 0))
(assert (<= second 59))

; Test Case 1: getDesiredFormat test
(push)
(echo "Test case for getDesiredFormat")
(assert (= year 2023))
(assert (= month 6))
(assert (= day 15))
(check-sat)
(get-model)
(pop)

; Test Case 2: parseDate test - basic date format
(push)
(echo "Test case for parseDate - basic format")
(assert (= year 2023))
(assert (= month 7))
(assert (= day 20))
(check-sat)
(get-model)
(pop)

; Test Case 3: parseDate test - with time format
(push)
(echo "Test case for parseDate - with time")
(assert (= year 2023))
(assert (= month 8))
(assert (= day 10))
(assert (= hour 14))
(assert (= minute 30))
(check-sat)
(get-model)
(pop)

; Test Case 4: getDaysBetweenTwoDate test - simple difference
(push)
(echo "Test case for getDaysBetweenTwoDate - simple difference")
(declare-const day1 Int)
(declare-const day2 Int)
(assert (= year 2023))
(assert (= month 6))
(assert (= day1 10))
(assert (= day2 15)) ; 5 days difference
(check-sat)
(get-model)
(pop)

; Test Case 5: getDaysBetweenTwoDate test - cross month
(push)
(echo "Test case for getDaysBetweenTwoDate - cross month")
(declare-const day1 Int)
(declare-const month1 Int)
(declare-const day2 Int)
(declare-const month2 Int)
(assert (= year 2023))
(assert (= month1 1)) ; January
(assert (= day1 31)) ; Jan 31
(assert (= month2 2)) ; February
(assert (= day2 3))  ; Feb 3
(check-sat)
(get-model)
(pop)

; Test Case 6: getDaysBetweenTwoDate test - cross year
(push)
(echo "Test case for getDaysBetweenTwoDate - cross year")
(declare-const day1 Int)
(declare-const month1 Int)
(declare-const year1 Int)
(declare-const day2 Int)
(declare-const month2 Int)
(declare-const year2 Int)
(assert (= year1 2023))
(assert (= month1 12)) ; December
(assert (= day1 31)) ; Dec 31
(assert (= year2 2024)) ; Next year
(assert (= month2 1))  ; January
(assert (= day2 5))    ; Jan 5
(check-sat)
(get-model)
(pop)

; Generate all test cases
(check-sat)
(get-model)
