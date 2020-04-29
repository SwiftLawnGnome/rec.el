;;; rec-tests.el --- Tests for rec -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Zach Shaftel
;;
;; Author: Zach Shaftel <http://github/SwiftLawnGnome>
;; Maintainer: Zach Shaftel <zshaftel@gmail.com>
;; Created: April 25, 2020
;; Modified: April 25, 2020
;; Version: 0.0.1
;; Keywords:
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;;  Tests for tco
;;
;;; Code:

(require 'rec (expand-file-name "rec.el"))
(require 'ert)
(require 'dash)

;; TODO
(ert-deftest rec-let ()
  (should (let ((n (number-sequence 0 100)))
            (rec-let ([nums n] [sum 0])
              (if (null nums)
                  (= sum (-sum n))
                (rec (cdr nums) (+ sum (car nums))))))))

(provide 'rec-tests)
;;; rec-tests.el ends here
