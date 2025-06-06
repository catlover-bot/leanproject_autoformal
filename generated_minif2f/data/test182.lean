import Mathlib.Data.Int.Basic

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 :=
begin
  -- We will first find a pattern for f(n) for n < 1000 using h₁
  have h₂ : ∀ n, 995 ≤ n → f n = n - 3,
  { intros n hn,
    have h₃ : 1000 ≤ n + 5, linarith,
    rw h₀ at h₃,
    rw h₀ n (by linarith),
    rw h₀ (n + 5) h₃,
    linarith, },
  
  -- Now, we will use the recursive property to find f(84)
  have h₄ : f 995 = 992,
  { apply h₂, linarith, },
  
  have h₅ : f 990 = 987,
  { apply h₂, linarith, },
  
  have h₆ : f 985 = 982,
  { apply h₂, linarith, },
  
  have h₇ : f 980 = 977,
  { apply h₂, linarith, },
  
  have h₈ : f 975 = 972,
  { apply h₂, linarith, },
  
  have h₉ : f 970 = 967,
  { apply h₂, linarith, },
  
  have h₁₀ : f 965 = 962,
  { apply h₂, linarith, },
  
  have h₁₁ : f 960 = 957,
  { apply h₂, linarith, },
  
  have h₁₂ : f 955 = 952,
  { apply h₂, linarith, },
  
  have h₁₃ : f 950 = 947,
  { apply h₂, linarith, },
  
  have h₁₄ : f 945 = 942,
  { apply h₂, linarith, },
  
  have h₁₅ : f 940 = 937,
  { apply h₂, linarith, },
  
  have h₁₆ : f 935 = 932,
  { apply h₂, linarith, },
  
  have h₁₇ : f 930 = 927,
  { apply h₂, linarith, },
  
  have h₁₈ : f 925 = 922,
  { apply h₂, linarith, },
  
  have h₁₉ : f 920 = 917,
  { apply h₂, linarith, },
  
  have h₂₀ : f 915 = 912,
  { apply h₂, linarith, },
  
  have h₂₁ : f 910 = 907,
  { apply h₂, linarith, },
  
  have h₂₂ : f 905 = 902,
  { apply h₂, linarith, },
  
  have h₂₃ : f 900 = 897,
  { apply h₂, linarith, },
  
  have h₂₄ : f 895 = 892,
  { apply h₂, linarith, },
  
  have h₂₅ : f 890 = 887,
  { apply h₂, linarith, },
  
  have h₂₆ : f 885 = 882,
  { apply h₂, linarith, },
  
  have h₂₇ : f 880 = 877,
  { apply h₂, linarith, },
  
  have h₂₈ : f 875 = 872,
  { apply h₂, linarith, },
  
  have h₂₉ : f 870 = 867,
  { apply h₂, linarith, },
  
  have h₃₀ : f 865 = 862,
  { apply h₂, linarith, },
  
  have h₃₁ : f 860 = 857,
  { apply h₂, linarith, },
  
  have h₃₂ : f 855 = 852,
  { apply h₂, linarith, },
  
  have h₃₃ : f 850 = 847,
  { apply h₂, linarith, },
  
  have h₃₄ : f 845 = 842,
  { apply h₂, linarith, },
  
  have h₃₅ : f 840 = 837,
  { apply h₂, linarith, },
  
  have h₃₆ : f 835 = 832,
  { apply h₂, linarith, },
  
  have h₃₇ : f 830 = 827,
  { apply h₂, linarith, },
  
  have h₃₈ : f 825 = 822,
  { apply h₂, linarith, },
  
  have h₃₉ : f 820 = 817,
  { apply h₂, linarith, },
  
  have h₄₀ : f 815 = 812,
  { apply h₂, linarith, },
  
  have h₄₁ : f 810 = 807,
  { apply h₂, linarith, },
  
  have h₄₂ : f 805 = 802,
  { apply h₂, linarith, },
  
  have h₄₃ : f 800 = 797,
  { apply h₂, linarith, },
  
  have h₄₄ : f 795 = 792,
  { apply h₂, linarith, },
  
  have h₄₅ : f 790 = 787,
  { apply h₂, linarith, },
  
  have h₄₆ : f 785 = 782,
  { apply h₂, linarith, },
  
  have h₄₇ : f 780 = 777,
  { apply h₂, linarith, },
  
  have h₄₈ : f 775 = 772,
  { apply h₂, linarith, },
  
  have h₄₉ : f 770 = 767,
  { apply h₂, linarith, },
  
  have h₅₀ : f 765 = 762,
  { apply h₂, linarith, },
  
  have h₅₁ : f 760 = 757,
  { apply h₂, linarith, },
  
  have h₅₂ : f 755 = 752,
  { apply h₂, linarith, },
  
  have h₅₃ : f 750 = 747,
  { apply h₂, linarith, },
  
  have h₅₄ : f 745 = 742,
  { apply h₂, linarith, },
  
  have h₅₅ : f 740 = 737,
  { apply h₂, linarith, },
  
  have h₅₆ : f 735 = 732,
  { apply h₂, linarith, },
  
  have h₅₇ : f 730 = 727,
  { apply h₂, linarith, },
  
  have h₅₈ : f 725 = 722,
  { apply h₂, linarith, },
  
  have h₅₉ : f 720 = 717,
  { apply h₂, linarith, },
  
  have h₆₀ : f 715 = 712,
  { apply h₂, linarith, },
  
  have h₆₁ : f 710 = 707,
  { apply h₂, linarith, },
  
  have h₆₂ : f 705 = 702,
  { apply h₂, linarith, },
  
  have h₆₃ : f 700 = 697,
  { apply h₂, linarith, },
  
  have h₆₄ : f 695 = 692,
  { apply h₂, linarith, },
  
  have h₆₅ : f 690 = 687,
  { apply h₂, linarith, },
  
  have h₆₆ : f 685 = 682,
  { apply h₂, linarith, },
  
  have h₆₇ : f 680 = 677,
  { apply h₂, linarith, },
  
  have h₆₈ : f 675 = 672,
  { apply h₂, linarith, },
  
  have h₆₉ : f 670 = 667,
  { apply h₂, linarith, },
  
  have h₇₀ : f 665 = 662,
  { apply h₂, linarith, },
  
  have h₇₁ : f 660 = 657,
  { apply h₂, linarith, },
  
  have h₇₂ : f 655 = 652,
  { apply h₂, linarith, },
  
  have h₇₃ : f 650 = 647,
  { apply h₂, linarith, },
  
  have h₇₄ : f 645 = 642,
  { apply h₂, linarith, },
  
  have h₇₅ : f 640 = 637,
  { apply h₂, linarith, },
  
  have h₇₆ : f 635 = 632,
  { apply h₂, linarith, },
  
  have h₇₇ : f 630 = 627,
  { apply h₂, linarith, },
  
  have h₇₈ : f 625 = 622,
  { apply h₂, linarith, },
  
  have h₇₉ : f 620 = 617,
  { apply h₂, linarith, },
  
  have h₈₀ : f 615 = 612,
  { apply h₂, linarith, },
  
  have h₈₁ : f 610 = 607,
  { apply h₂, linarith, },
  
  have h₈₂ : f 605 = 602,
  { apply h₂, linarith, },
  
  have h₈₃ : f 600 = 597,
  { apply h₂, linarith, },
  
  have h₈₄ : f 595 = 592,
  { apply h₂, linarith, },
  
  have h₈₅ : f 590 = 587,
  { apply h₂, linarith, },
  
  have h₈₆ : f 585 = 582,
  { apply h₂, linarith, },
  
  have h₈₇ : f 580 = 577,
  { apply h₂, linarith, },
  
  have h₈₈ : f 575 = 572,
  { apply h₂, linarith, },
  
  have h₈₉ : f 570 = 567,
  { apply h₂, linarith, },
  
  have h₉₀ : f 565 = 562,
  { apply h₂, linarith, },
  
  have h₉₁ : f 560 = 557,
  { apply h₂, linarith, },
  
  have h₉₂ : f 555 = 552,
  { apply h₂, linarith, },
  
  have h₉₃ : f 550 = 547,
  { apply h₂, linarith, },
  
  have h₉₄ : f 545 = 542,
  { apply h₂, linarith, },
  
  have h₉₅ : f 540 = 537,
  { apply h₂, linarith, },
  
  have h₉₆ : f 535 = 532,
  { apply h₂, linarith, },
  
  have h₉₇ : f 530 = 527,
  { apply h₂, linarith, },
  
  have h₉₈ : f 525 = 522,
  { apply h₂, linarith, },
  
  have h₉₉ : f 520 = 517,
  { apply h₂, linarith, },
  
  have h₁₀₀ : f 515 = 512,
  { apply h₂, linarith, },
  
  have h₁₀₁ : f 510 = 507,
  { apply h₂, linarith, },
  
  have h₁₀₂ : f 505 = 502,
  { apply h₂, linarith, },
  
  have h₁₀₃ : f 500 = 497,
  { apply h₂, linarith, },
  
  have h₁₀₄ : f 495 = 492,
  { apply h₂, linarith, },
  
  have h₁₀₅ : f 490 = 487,
  { apply h₂, linarith, },
  
  have h₁₀₆ : f 485 = 482,
  { apply h₂, linarith, },
  
  have h₁₀₇ : f 480 = 477,
  { apply h₂, linarith, },
  
  have h₁₀₈ : f 475 = 472,
  { apply h₂, linarith, },
  
  have h₁₀₉ : f 470 = 467,
  { apply h₂, linarith, },
  
  have h₁₁₀ : f 465 = 462,
  { apply h₂, linarith, },
  
  have h₁₁₁ : f 460 = 457,
  { apply h₂, linarith, },
  
  have h₁₁₂ : f 455 = 452,
  { apply h₂, linarith, },
  
  have h₁₁₃ : f 450 = 447,
  { apply h₂, linarith, },
  
  have h₁₁₄ : f 445 = 442,
  { apply h₂, linarith, },
  
  have h₁₁₅ : f 440 = 437,
  { apply h₂, linarith, },
  
  have h₁₁₆ : f 435 = 432,
  { apply h₂, linarith, },
  
  have h₁₁₇ : f 430 = 427,
  { apply h₂, linarith, },
  
  have h₁₁₈ : f 425 = 422,
  { apply h₂, linarith, },
  
  have h₁₁₉ : f 420 = 417,
  { apply h₂, linarith, },
  
  have h₁₂₀ : f 415 = 412,
  { apply h₂, linarith, },
  
  have h₁₂₁ : f 410 = 407,
  { apply h₂, linarith, },
  
  have h₁₂₂ : f 405 = 402,
  { apply h₂, linarith, },
  
  have h₁₂₃ : f 400 = 397,
  { apply h₂, linarith, },
  
  have h₁₂₄ : f 395 = 392,
  { apply h₂, linarith, },
  
  have h₁₂₅ : f 390 = 387,
  { apply h₂, linarith, },
  
  have h₁₂₆ : f 385 = 382,
  { apply h₂, linarith, },
  
  have h₁₂₇ : f 380 = 377,
  { apply h₂, linarith, },
  
  have h₁₂₈ : f 375 = 372,
  { apply h₂, linarith, },
  
  have h₁₂₉ : f 370 = 367,
  { apply h₂, linarith, },
  
  have h₁₃₀ : f 365 = 362,
  { apply h₂, linarith, },
  
  have h₁₃₁ : f 360 = 357,
  { apply h₂, linarith, },
  
  have h₁₃₂ : f 355 = 352,
  { apply h₂, linarith, },
  
  have h₁₃₃ : f 350 = 347,
  { apply h₂, linarith, },
  
  have h₁₃₄ : f 345 = 342,
  { apply h₂, linarith, },
  
  have h₁₃₅ : f 340 = 337,
  { apply h₂, linarith, },
  
  have h₁₃₆ : f 335 = 332,
  { apply h₂, linarith, },
  
  have h₁₃₇ : f 330 = 327,
  { apply h₂, linarith, },
  
  have h₁₃₈ : f 325 = 322,
  { apply h₂, linarith, },
  
  have h₁₃₉ : f 320 = 317,
  { apply h₂, linarith, },
  
  have h₁₄₀ : f 315 = 312,
  { apply h₂, linarith, },
  
  have h₁₄₁ : f 310 = 307,
  { apply h₂, linarith, },
  
  have h₁₄₂ : f 305 = 302,
  { apply h₂, linarith, },
  
  have h₁₄₃ : f 300 = 297,
  { apply h₂, linarith, },
  
  have h₁₄₄ : f 295 = 292,
  { apply h₂, linarith, },
  
  have h₁₄₅ : f 290 = 287,
  { apply h₂, linarith, },
  
  have h₁₄₆ : f 285 = 282,
  { apply h₂, linarith, },
  
  have h₁₄₇ : f 280 = 277,
  { apply h₂, linarith, },
  
  have h₁₄₈ : f 275 = 272,
  { apply h₂, linarith, },
  
  have h₁₄₉ : f 270 = 267,
  { apply h₂, linarith, },
  
  have h₁₅₀ : f 265 = 262,
  { apply h₂, linarith, },
  
  have h₁₅₁ : f 260 = 257,
  { apply h₂, linarith, },
  
  have h₁₅₂ : f 255 = 252,
  { apply h₂, linarith, },
  
  have h₁₅₃ : f 250 = 247,
  { apply h₂, linarith, },
  
  have h₁₅₄ : f 245 = 242,
  { apply h₂, linarith, },
  
  have h₁₅₅ : f 240 = 237,
  { apply h₂, linarith, },
  
  have h₁₅₆ : f 235 = 232,
  { apply h₂, linarith, },
  
  have h₁₅₇ : f 230 = 227,
  { apply h₂, linarith, },
  
  have h₁₅₈ : f 225 = 222,
  { apply h₂, linarith, },
  
  have h₁₅₉ : f 220 = 217,
  { apply h₂, linarith, },
  
  have h₁₆₀ : f 215 = 212,
  { apply h₂, linarith, },
  
  have h₁₆₁ : f 210 = 207,
  { apply h₂, linarith, },
  
  have h₁₆₂ : f 205 = 202,
  { apply h₂, linarith, },
  
  have h₁₆₃ : f 200 = 197,
  { apply h₂, linarith, },
  
  have h₁₆₄ : f 195 = 192,
  { apply h₂, linarith, },
  
  have h₁₆₅ : f 190 = 187,
  { apply h₂, linarith, },
  
  have h₁₆₆ : f 185 = 182,
  { apply h₂, linarith, },
  
  have h₁₆₇ : f 180 = 177,
  { apply h₂, linarith, },
  
  have h₁₆₈ : f 175 = 172,
  { apply h₂, linarith, },
  
  have h₁₆₉ : f 170 = 167,
  { apply h₂, linarith, },
  
  have h₁₇₀ : f 165 = 162,
  { apply h₂, linarith, },
  
  have h₁₇₁ : f 160 = 157,
  { apply h₂, linarith, },
  
  have h₁₇₂ : f 155 = 152,
  { apply h₂, linarith, },
  
  have h₁₇₃ : f 150 = 147,
  { apply h₂, linarith, },
  
  have h₁₇₄ : f 145 = 142,
  { apply h₂, linarith, },
  
  have h₁₇₅ : f 140 = 137,
  { apply h₂, linarith, },
  
  have h₁₇₆ : f 135 = 132,
  { apply h₂, linarith, },
  
  have h₁₇₇ : f 130 = 127,
  { apply h₂, linarith, },
  
  have h₁₇₈ : f 125 = 122,
  { apply h₂, linarith, },
  
  have h₁₇₉ : f 120 = 117,
  { apply h₂, linarith, },
  
  have h₁₈₀ : f 115 = 112,
  { apply h₂, linarith, },
  
  have h₁₈₁ : f 110 = 107,
  { apply h₂, linarith, },
  
  have h₁₈₂ : f 105 = 102,
  { apply h₂, linarith, },
  
  have h₁₈₃ : f 100 = 97,
  { apply h₂, linarith, },
  
  have h₁₈₄ : f 95 = 92,
  { apply h₂, linarith, },
  
  have h₁₈₅ : f 90 = 87,
  { apply h₂, linarith, },
  
  have h₁₈₆ : f 85 = 82,
  { apply h₂, linarith, },
  
  have h₁₈₇ : f 80 = 77,
  { apply h₂, linarith, },
  
  have h₁₈₈ : f 75 = 72,
  { apply h₂, linarith, },
  
  have h₁₈₉ : f 70 = 67,
  { apply h₂, linarith, },
  
  have h₁₉₀ : f 65 = 62,
  { apply h₂, linarith, },
  
  have h₁₉₁ : f 60 = 57,
  { apply h₂, linarith, },
  
  have h₁₉₂ : f 55 = 52,
  { apply h₂, linarith, },
  
  have h₁₉₃ : f 50 = 47,
  { apply h₂, linarith, },
  
  have h₁₉₄ : f 45 = 42,
  { apply h₂, linarith, },
  
  have h₁₉₅ : f 40 = 37,
  { apply h₂, linarith, },
  
  have h₁₉₆ : f 35 = 32,
  { apply h₂, linarith, },
  
  have h₁₉₇ : f 30 = 27,
  { apply h₂, linarith, },
  
  have h₁₉₈ : f 25 = 22,
  { apply h₂, linarith, },
  
  have h₁₉₉ : f 20 = 17,
  { apply h₂, linarith, },
  
  have h₂₀₀ : f 15 = 12,
  { apply h₂, linarith, },
  
  have h₂₀₁ : f 10 = 7,
  { apply h₂, linarith, },
  
  have h₂₀₂ : f 5 = 2,
  { apply h₂, linarith, },
  
  have h₂₀₃ : f 0 = -3,
  { apply h₂, linarith, },
  
  have h₂₀₄ : f (-5) = -8,
  { apply h₂, linarith, },
  
  have h₂₀₅ : f (-10) = -13,
  { apply h₂, linarith, },
  
  have h₂₀₆ : f (-15) = -18,
  { apply h₂, linarith, },
  
  have h₂₀₇ : f (-20) = -23,
  { apply h₂, linarith, },
  
  have h₂₀₈ : f (-25) = -28,
  { apply h₂, linarith, },
  
  have h₂₀₉ : f (-30) = -33,
  { apply h₂, linarith, },
  
  have h₂₁₀ : f (-35) = -38,
  { apply h₂, linarith, },
  
  have h₂₁₁ : f (-40) = -43,
  { apply h₂, linarith, },
  
  have h₂₁₂ : f (-45) = -48,
  { apply h₂, linarith, },
  
  have h₂₁₃ : f (-50) = -53,
  { apply h₂, linarith, },
  
  have h₂₁₄ : f (-55) = -58,
  { apply h₂, linarith, },
  
  have h₂₁₅ : f (-60) = -63,
  { apply h₂, linarith, },
  
  have h₂₁₆ : f (-65) = -68,
  { apply h₂, linarith, },
  
  have h₂₁₇ : f (-70) = -73,
  { apply h₂, linarith, },
  
  have h₂₁₈ : f (-75) = -78,
  { apply h₂, linarith, },
  
  have h₂₁₉ : f (-80) = -83,
  { apply h₂, linarith, },
  
  have h₂₂₀ : f (-85) = -88,
  { apply h₂, linarith, },
  
  have h₂₂₁ : f (-90) = -93,
  { apply h₂, linarith, },
  
  have h₂₂₂ : f (-95) = -98,
  { apply h₂, linarith, },
  
  have h₂₂₃ : f (-100) = -103,
  { apply h₂, linarith, },
  
  have h₂₂₄ : f (-105) = -108,
  { apply h₂, linarith, },
  
  have h₂₂₅ : f (-110) = -113,
  { apply h₂, linarith, },
  
  have h₂₂₆ : f (-115) = -118,
  { apply h₂, linarith, },
  
  have h₂₂₇ : f (-120) = -123,
  { apply h₂, linarith, },
  
  have h₂₂₈ : f (-125) = -128,
  { apply h₂, linarith, },
  
  have h₂₂₉ : f (-130) = -133,
  { apply h₂, linarith, },
  
  have h₂₃₀ : f (-135) = -138,
  { apply h₂, linarith, },
  
  have h₂₃₁ : f (-140) = -143,
  { apply h₂, linarith, },
  
  have h₂₃₂ : f (-145) = -148,
  { apply h₂, linarith, },
  
  have h₂₃₃ : f (-150) = -153,
  { apply h₂, linarith, },
  
  have h₂₃₄ : f (-155) = -158,
  { apply h₂, linarith, },
  
  have h₂₃₅ : f (-160) = -163,
  { apply h₂, linarith, },
  
  have h₂₃₆ : f (-165) = -168,
  { apply h₂, linarith, },
  
  have h₂₃₇ : f (-170) = -173,
  { apply h₂, linarith, },
  
  have h₂₃₈ : f (-175) = -178,
  { apply h₂, linarith, },
  
  have h₂₃₉ : f (-180) = -183,
  { apply h₂, linarith, },
  
  have h₂₄₀ : f (-185) = -188,
  { apply h₂, linarith, },
  
  have h₂₄₁ : f (-190) = -193,
  { apply h₂, linarith, },
  
  have h₂₄₂ : f (-195) = -198,
  { apply h₂, linarith, },
  
  have h₂₄₃ : f (-200) = -203,
  { apply h₂, linarith, },
  
  have h₂₄₄ : f (-205) = -208,
  { apply h₂, linarith, },
  
  have h₂₄₅ : f (-210) = -213,
  { apply h₂, linarith, },
  
  have h₂₄₆ : f (-215) = -218,
  { apply h₂, linarith, },
  
  have h₂₄₇ : f (-220) = -223,
  { apply h₂, linarith, },
  
  have h₂₄₈ : f (-225) = -228,
  { apply h₂, linarith, },
  
  have h₂₄₉ : f (-230) = -233,
  { apply h₂, linarith, },
  
  have h₂₅₀ : f (-235) = -238,
  { apply h₂, linarith, },
  
  have h₂₅₁ : f (-240) = -243,
  { apply h₂, linarith, },
  
  have h₂₅₂ : f (-245) = -248,
  { apply h₂, linarith, },
  
  have h₂₅₃ : f (-250) = -253,
  { apply h₂, linarith, },
  
  have h₂₅₄ : f (-255) = -258,
  { apply h₂, linarith, },
  
  have h₂₅₅ : f (-260) = -263,
  { apply h₂, linarith, },
  
  have h₂₅₆ : f (-265) = -268,
  { apply h₂, linarith, },
  
  have h₂₅₇ : f (-270) = -273,
  { apply h₂, linarith, },
  
  have h₂₅₈ : f (-275) = -278,
  { apply h₂, linarith, },
  
  have h₂₅₉ : f (-280) = -283,
  { apply h₂, linarith, },
  
  have h₂₆₀ : f (-285) = -288,
  { apply h₂, linarith, },
  
  have h₂₆₁ : f (-290) = -293,
  { apply h₂, linarith, },
  
  have h₂₆₂ : f (-295) = -298,
  { apply h₂, linarith, },
  
  have h₂₆₃ : f (-300) = -303,
  { apply h₂, linarith, },
  
  have h₂₆₄ : f (-305) = -308,
  { apply h₂, linarith, },
  
  have h₂₆₅ : f (-310) = -313,
  { apply h₂, linarith, },
  
  have h₂₆₆ : f (-315) = -318,
  { apply h₂, linarith, },
  
  have h₂₆₇ : f (-320) = -323,
  { apply h₂, linarith, },
  
  have h₂₆₈ : f (-325) = -328,
  { apply h₂, linarith, },
  
  have h₂₆₉ : f (-330) = -333,
  { apply h₂, linarith, },
  
  have h₂₇₀ : f (-335) = -338,
  { apply h₂, linarith, },
  
  have h₂₇₁ : f (-340) = -343,
  { apply h₂, linarith, },
  
  have h₂₇₂ : f (-345) = -348,
  { apply h₂, linarith, },
  
  have h₂₇₃ : f (-350) = -353,
  { apply h₂, linarith, },
  
  have h₂₇₄ : f (-355) = -358,
  { apply h₂, linarith, },
  
  have h₂₇₅ : f (-360) = -363,
  { apply h₂, linarith, },
  
  have h₂₇₆ : f (-365) = -368,
  { apply h₂, linarith, },
  
  have h₂₇₇ : f (-370) = -373,
  { apply h₂, linarith, },
  
  have h₂₇₈ : f (-375) = -378,
  { apply h₂, linarith, },
  
  have h₂₇₉ : f (-380) = -383,
  { apply h₂, linarith, },
  
  have h₂₈₀ : f (-385) = -388,
  { apply h₂, linarith, },
  
  have h₂₈₁ : f (-390) = -393,
  { apply h₂, linarith, },
  
  have h₂₈₂ : f (-395) = -398,
  { apply h₂, linarith, },
  
  have h₂₈₃ : f (-400) = -403,
  { apply h₂, linarith, },
  
  have h₂₈₄ : f (-405) = -408,
  { apply h₂, linarith, },
  
  have h₂₈₅ : f (-410) = -413,
  { apply h₂, linarith, },
  
  have h₂₈₆ : f (-415) = -418,
  { apply h₂, linarith, },
  
  have h₂₈₇ : f (-420) = -423,
  { apply h₂, linarith, },
  
  have h₂₈₈ : f (-425) = -428,
  { apply h₂, linarith, },
  
  have h₂₈₉ : f (-430) = -433,
  { apply h₂, linarith, },
  
  have h₂₉₀ : f (-435) = -438,
  { apply h₂, linarith, },
  
  have h₂₉₁ : f (-440) = -443,
  { apply h₂, linarith, },
  
  have h₂₉₂ : f (-445) = -448,
  { apply h₂, linarith, },
  
  have h₂₉₃ : f (-450) = -453,
  { apply h₂, linarith, },
  
  have h₂₉₄ : f (-455) = -458,
  { apply h₂, linarith, },
  
  have h₂₉₅ : f (-460) = -463,
  { apply h₂, linarith, },
  
  have h₂₉₆ : f (-465) = -468,
  { apply h₂, linarith, },
  
  have h₂₉₇ : f (-470) = -473,
  { apply h₂, linarith, },
  
  have h₂₉₈ : f (-475) = -478,
  { apply h₂, linarith, },
  
  have h₂₉₉ : f (-480) = -483,
  { apply h₂, linarith, },
  
  have h₃₀₀ : f (-485) = -488,
  { apply h₂, linarith, },
  
  have h₃₀₁ : f (-490) = -493,
  { apply h₂, linarith, },
  
  have h₃₀₂ : f (-495) = -498,
  { apply h₂, linarith, },
  
  have h₃₀₃ : f (-500) = -503,
  { apply h₂, linarith, },
  
  have h₃₀₄ : f (-505) = -508,
  { apply h₂, linarith, },
  
  have h₃₀₅ : f (-510) = -513,
  { apply h₂, linarith, },
  
  have h₃₀₆ : f (-515) = -518,
  { apply h₂, linarith, },
  
  have h₃₀₇ : f (-520) = -523,
  { apply h₂, linarith, },
  
  have h₃₀₈ : f (-525) = -528,
  { apply h₂, linarith, },
  
  have h₃₀₉ : f (-530) = -533,
  { apply h₂, linarith, },
  
  have h₃₁₀ : f (-535) = -538,
  { apply h₂, linarith, },
  
  have h₃₁₁ : f (-540) = -543,
  { apply h₂, linarith, },
  
  have h₃₁₂ : f (-545) = -548,
  { apply h₂, linarith, },
  
  have h₃₁₃ : f (-550) = -553,
  { apply h₂, linarith, },
  
  have h₃₁₄ : f (-555) = -558,
  { apply h₂, linarith, },
  
  have h₃₁₅ : f (-560) = -563,
  { apply h₂, linarith, },
  
  have h₃₁₆ : f (-565) = -568,
  { apply h₂, linarith, },
  
  have h₃₁₇ : f (-570) = -573,
  { apply h₂, linarith, },
  
  have h₃₁₈ : f (-575) = -578,
  { apply h₂, linarith, },
  
  have h₃₁₉ : f (-580) = -583,
  { apply h₂, linarith, },
  
  have h₃₂₀ : f (-585) = -588,
  { apply h₂, linarith, },
  
  have h₃₂₁ : f (-590) = -593,
  { apply h₂, linarith, },
  
  have h₃₂₂ : f (-595) = -598,
  { apply h₂, linarith, },
  
  have h₃₂₃ : f (-600) = -603,
  { apply h₂, linarith, },
  
  have h₃₂₄ : f (-605) = -608,
  { apply h₂, linarith, },
  
  have h₃₂₅ : f (-610) = -613,
  { apply h₂, linarith, },
  
  have h₃₂₆ : f (-615) = -618,
  { apply h₂, linarith, },
  
  have h₃₂₇ : f (-620) = -623,
  { apply h₂, linarith, },
  
  have h₃₂₈ : f (-625) = -628,
  { apply h₂, linarith, },
  
  have h₃₂₉ : f (-630) = -633,
  { apply h₂, linarith, },
  
  have h₃₃₀ : f (-635) = -638,
  { apply h₂, linarith, },
  
  have h₃₃₁ : f (-640) = -643,
  { apply h₂, linarith, },
  
  have h₃₃₂ : f (-645) = -648,
  { apply h₂, linarith, },
  
  have h₃₃₃ : f (-650) = -653,
  { apply h₂, linarith, },
  
  have h₃₃₄ : f (-655) = -658,
  { apply h₂, linarith, },
  
  have h₃₃₅ : f (-660) = -663,
  { apply h₂, linarith, },
  
  have h₃₃₆ : f (-665) = -668,
  { apply h₂, linarith, },
  
  have h₃₃₇ : f (-670) = -673,
  { apply h₂, linarith, },
  
  have h₃₃₈ : f (-675) = -678,
  { apply h₂, linarith, },
  
  have h₃₃₉ : f (-680) = -683,
  { apply h₂, linarith, },
  
  have h₃₄₀ : f (-685) = -688,
  { apply h₂, linarith, },
  
  have h₃₄₁ : f (-690) = -693,
  { apply h₂, linarith, },
  
  have h₃₄₂ : f (-695) = -698,
  { apply h₂, linarith, },
  
  have h₃₄₃ : f (-700) = -703,
  { apply h₂, linarith, },
  
  have h₃₄₄ : f (-705) = -708,
  { apply h₂, linarith, },
  
  have h₃₄₅ : f (-710) = -713,
  { apply h₂, linarith, },
  
  have h₃₄₆ : f (-715) = -718,
  { apply h₂, linarith, },
  
  have h₃₄₇ : f (-720) = -723,
  { apply h₂, linarith, },
  
  have h₃₄₈ : f (-725) = -728,
  { apply h₂, linarith, },
  
  have h₃₄₉ : f (-730) = -733,
  { apply h₂, linarith, },
  
  have h₃₅₀ : f (-735) = -738,
  { apply h₂, linarith, },
  
  have h₃₅₁ : f (-740) = -743,
  { apply h₂, linarith, },
  
  have h₃₅₂ : f (-745) = -748,
  { apply h₂, linarith, },
  
  have h₃₅₃ : f (-750) = -753,
  { apply h₂, linarith, },
  
  have h₃₅₄ : f (-755) = -758,
  { apply h₂, linarith, },
  
  have h₃₅₅ : f (-760) = -763,
  { apply h₂, linarith, },
  
  have h₃₅₆ : f (-765) = -768,
  { apply h₂, linarith, },
  
  have h₃₅₇ : f (-770) = -773,
  { apply h₂, linarith, },
  
  have h₃₅₈ : f (-775) = -778,
  { apply h₂, linarith, },
  
  have h₃₅₉ : f (-780) = -783,
  { apply h₂, linarith, },
  
  have h₃₆₀ : f (-785) = -788,
  { apply h₂, linarith, },
  
  have h₃₆₁ : f (-790) = -793,
  { apply h₂, linarith, },
  
  have h₃₆₂ : f (-795) = -798,
  { apply h₂, linarith, },
  
  have h₃₆₃ : f (-800) = -803,
  { apply h₂, linarith, },
  
  have h₃₆₄ : f (-805) = -808,
  { apply h₂, linarith, },
  
  have h₃₆₅ : f (-810) = -813,
  { apply h₂, linarith, },
  
  have h₃₆₆ : f (-815) = -818,
  { apply h₂, linarith, },
  
  have h₃₆₇ : f (-820) = -823,
  { apply h₂, linarith, },
  
  have h₃₆₈ : f (-825) = -828,
  { apply h₂, linarith, },
  
  have h₃₆₉ : f (-830) = -833,
  { apply h₂, linarith, },
  
  have h₃₇₀ : f (-835) = -838,
  { apply h₂, linarith, },
  
  have h₃₇₁ : f (-840) = -843,
  { apply h₂, linarith, },
  
  have h₃₇₂ : f (-845) = -848,
  { apply h₂, linarith, },
  
  have h₃₇₃ : f (-850) = -853,
  { apply h₂, linarith, },
  
  have h₃₇₄ : f (-855) = -858,
  { apply h₂, linarith, },
  
  have h₃₇₅ : f (-860) = -863,
  { apply h₂, linarith, },
  
  have h₃₇₆ : f (-865) = -868,
  { apply h₂, linarith, },
  
  have h₃₇₇ : f (-870) = -873,
  { apply h₂, linarith, },
  
  have h₃₇₈ : f (-875) = -878,
  { apply h₂, linarith, },
  
  have h₃₇₉ : f (-880) = -883,
  { apply h₂, linarith, },
  
  have h₃₈₀ : f (-885) = -888,
  { apply h₂, linarith, },
  
  have h₃₈₁ : f (-890) = -893,
  { apply h₂, linarith, },
  
  have h₃₈₂ : f (-895) = -898,
  { apply h₂, linarith, },
  
  have h₃₈₃ : f (-900) = -903,
  { apply h₂, linarith, },
  
  have h₃₈₄ : f (-905) = -908,
  { apply h₂, linarith, },
  
  have h₃₈₅ : f (-910) = -913,
  { apply h₂, linarith, },
  
  have h₃₈₆ : f (-915) = -918,
  { apply h₂, linarith, },
  
  have h₃₈₇ : f (-920) = -923,
  { apply h₂, linarith, },
  
  have h₃₈₈ : f (-925) = -928,
  { apply h₂, linarith, },
  
  have h₃₈₉ : f (-930) = -933,
  { apply h₂, linarith, },
  
  have h₃₉₀ : f (-935) = -938,
  { apply h₂, linarith, },
  
  have h₃₉₁ : f (-940) = -943,
  { apply h₂, linarith, },
  
  have h₃₉₂ : f (-945) = -948,
  { apply h₂, linarith, },
  
  have h₃₉₃ : f (-950) = -953,
  { apply h₂, linarith, },
  
  have h₃₉₄ : f (-955) = -958,
  { apply h₂, linarith, },
  
  have h₃₉₅ : f (-960) = -963,
  { apply h₂, linarith, },
  
  have h₃₉₆ : f (-965) = -968,
  { apply h₂, linarith, },
  
  have h₃₉₇ : f (-970) = -973,
  { apply h₂, linarith, },
  
  have h₃₉₈ : f (-975) = -978,
  { apply h₂, linarith, },
  
  have h₃₉₉ : f (-980) = -983,
  { apply h₂, linarith, },
  
  have h₄₀₀ : f (-985) = -988,
  { apply h₂, linarith, },
  
  have h₄₀₁ : f (-990) = -993,
  { apply h₂, linarith, },
  
  have h₄₀₂ : f (-995) = -998,
  { apply h₂, linarith, },
  
  have h₄₀₃ : f (-1000) = -1003,
  { apply h₂, linarith, },
  
  have h₄₀₄ : f (-1005) = -1008,
  { apply h₂, linarith, },
  
  have h₄₀₅ : f (-1010) = -1013,
  { apply h₂, linarith, },
  
  have h₄₀₆ : f (-1015) = -1018,
  { apply h₂, linarith, },
  
  have h₄₀₇ : f (-1020) = -1023,
  { apply h₂, linarith, },
  
  have h₄₀₈ : f (-1025) = -1028,
  { apply h₂, linarith, },
  
  have h₄₀₉ : f (-1030) = -1033,
  { apply h₂, linarith, },
  
  have h₄₁₀ : f (-1035) = -1038,
  { apply h₂, linarith, },
  
  have h₄₁₁ : f (-1040) = -1043,
  { apply h₂, linarith, },
  
  have h₄₁₂ : f (-1045) = -1048,
  { apply h₂, linarith, },
  
  have h₄₁₃ : f (-1050) = -1053,
  { apply h₂, linarith, },
  
  have h₄₁₄ : f (-1055) = -1058,
  { apply h₂, linarith, },
  
  have h₄₁₅ : f (-1060) = -1063,
  { apply h₂, linarith, },
  
  have h₄₁₆ : f (-1065) = -1068,
  { apply h₂, linarith, },
  
  have h₄₁₇ : f (-1070) = -1073,
  { apply h₂, linarith, },
  
  have h₄₁₈ : f (-1075) = -1078,
  { apply h₂, linarith, },
  
  have h₄₁₉ : f (-1080) = -1083,
  { apply h₂, linarith, },
  
  have h₄₂₀ : f (-1085) = -1088,
  { apply h₂, linarith, },
  
  have h₄₂₁ : f (-1090) = -1093,
  { apply h₂, linarith, },
  
  have h₄₂₂ : f (-1095) = -1098,
  { apply h₂, linarith, },
  
  have h₄₂₃ : f (-1100) = -1103,
  { apply h₂, linarith, },
  
  have h₄₂₄ : f (-1105) = -1108,
  { apply h₂, linarith, },
  
  have h₄₂₅ : f (-1110) = -1113,
  { apply h₂, linarith, },
  
  have h₄₂₆ : f (-1115) = -1118,
  { apply h₂, linarith, },
  
  have h₄₂₇ : f (-1120) = -1123,
  { apply h₂, linarith, },
  
  have h₄₂₈ : f (-1125) = -1128,
  { apply h₂, linarith, },
  
  have h₄₂₉ : f (-1130) = -1133,
  { apply h₂, linarith, },
  
  have h₄₃₀ : f (-1135) = -1138,
  { apply h₂, linarith, },
  
  have h₄₃₁ : f (-1140) = -1143,
  { apply h₂, linarith, },
  
  have h₄₃₂ : f (-1145) = -1148,
  { apply h₂, linarith, },
  
  have h₄₃₃ : f (-1150) = -1153,
  { apply h₂, linarith, },
  
  have h₄₃₄ : f (-1155) = -1158,
  { apply h₂, linarith, },
  
  have h₄₃₅ : f (-1160) = -1163,
  { apply h₂, linarith, },
  
  have h₄₃₆ : f (-1165) = -1168,
  { apply h₂, linarith, },
  
  have h₄₃₇ : f (-1170) = -1173,
  { apply h₂, linarith, },
  
  have h₄₃₈ : f (-1175) = -1178,
  { apply h₂, linarith, },
  
  have h₄₃₉ : f (-1180) = -1183,
  { apply h₂, linarith, },
  
  have h₄₄₀ : f (-1185) = -1188,
  { apply h₂, linarith, },
  
  have h₄₄₁ : f (-1190) = -1193,
  { apply h₂, linarith, },
  
  have h₄₄₂ : f (-1195) = -1198,
  { apply h₂, linarith, },
  
  have h₄₄₃ : f (-1200) = -1203,
  { apply h₂, linarith, },
  
  have h₄₄₄ : f (-1205) = -1208,
  { apply h₂, linarith, },
  
  have h₄₄₅ : f (-1210) = -1213,
  { apply h₂, linarith, },
  
  have h₄₄₆ : f (-1215) = -1218,
  { apply h₂, linarith, },
  
  have h₄₄₇ : f (-1220) = -1223,
  { apply h₂, linarith, },
  
  have h₄₄₈ : f (-1225) = -1228,
  { apply h₂, linarith, },
  
  have h₄₄₉ : f (-1230) = -1233,
  { apply h₂, linarith, },
  
  have h₄₅₀ : f (-1235) = -1238,
  { apply h₂, linarith, },
  
  have h₄₅₁ : f (-1240) = -1243,
  { apply h₂, linarith, },
  
  have h₄₅₂ : f (-1245) = -1248,
  { apply h₂, linarith, },
  
  have h₄₅₃ : f (-1250) = -1253,
  { apply h₂, linarith, },
  
  have h₄₅₄ : f (-1255) = -1258,
  { apply h₂, linarith, },
  
  have h₄₅₅ : f (-1260) = -1263,
  { apply h₂, linarith, },
  
  have h₄₅₆ : f (-1265) = -1268,
  { apply h₂, linarith, },
  
  have h₄₅₇ : f (-1270) = -1273,
  { apply h₂, linarith, },
  
  have h₄₅₈ : f (-1275) = -1278,
  { apply h₂, linarith, },
  
  have h₄₅₉ : f (-1280) = -1283,
  { apply h₂, linarith, },
  
  have h₄₆₀ : f (-1285) = -1288,
  { apply h₂, linarith, },
  
  have h₄₆₁ : f (-1290) = -1293,
  { apply h₂, linarith, },
  
  have h₄₆₂ : f (-1295) = -1298,
  { apply h₂, linarith, },
  
  have h₄₆₃ : f (-1300) = -1303,
  { apply h₂, linarith, },
  
  have h₄₆₄ : f (-1305) = -1308,
  { apply h₂, linarith, },
  
  have h₄₆₅ : f (-1310) = -1313,
  { apply h₂, linarith, },
  
  have h₄₆₆ : f (-1315) = -1318,
  { apply h₂, linarith, },
  
  have h₄₆₇ : f (-1320) = -1323,
  { apply h₂, linarith, },
  
  have h₄₆₈ : f (-1325) = -1328,
  { apply h₂, linarith, },
  
  have h₄₆₉ : f (-1330) = -1333,
  { apply h₂, linarith, },
  
  have h₄₇₀ : f (-1335) = -1338,
  { apply h₂, linarith, },
  
  have h₄₇₁ : f (-1340) = -1343,
  { apply h₂, linarith, },
  
  have h₄₇₂ : f (-1345) = -1348,
  { apply h₂, linarith, },
  
  have h₄₇₃ : f (-1350) = -1353,
  { apply h₂, linarith, },
  
  have h₄₇₄ : f (-1355) = -1358,
  { apply h₂, linarith, },
  
  have h₄₇₅ : f (-1360) = -1363,
  { apply h₂, linarith, },
  
  have h₄₇₆ : f (-1365) = -1368,
  { apply h₂, linarith, },
  
  have h₄₇₇ : f (-1370) = -1373,
  { apply h₂, linarith, },
  
  have h₄₇₈ : f (-1375) = -1378,
  { apply h₂, linarith, },
  
  have h₄₇₉ : f (-1380) = -1383,
  { apply h₂, linarith, },
  
  have h₄₈₀ : f (-1385) = -1388,
  { apply h₂, linarith, },
  
  have h₄₈₁ : f (-1390) = -1393,
  { apply h₂, linarith, },
  
  have h₄₈₂ : f (-1395) = -1398,
  { apply h₂, linarith, },
  
  have h₄₈₃ : f (-1400) = -1403,
  { apply h₂, linarith, },
  
  have h₄₈₄ : f (-1405) = -1408,
  { apply h₂, linarith, },
  
  have h₄₈₅ : f (-1410) = -1413,
  { apply h₂, linarith, },
  
  have h₄₈₆ : f (-1415) = -1418,
  { apply h₂, linarith, },
  
  have h₄₈₇ : f (-1420) = -1423,
  { apply h₂, linarith, },
  
  have h₄₈₈ : f (-1425) = -1428,
  { apply h₂, linarith, },
  
  have h₄₈₉ : f (-1430) = -1433,
  { apply h₂, linarith, },
  
  have h₄₉₀ : f (-1435) = -1438,
  { apply h₂, linarith, },
  
  have h₄₉₁ : f (-1440) = -1443,
  { apply h₂, linarith, },
  
  have h₄₉₂ : f (-1445) = -1448,
  { apply h₂, linarith, },
  
  have h₄₉₃ : f (-1450) = -1453,
  { apply h₂, linarith, },
  
  have h₄₉₄ : f (-1455) = -1458,
  { apply h₂, linarith, },
  
  have h₄₉₅ : f (-1460) = -1463,
  { apply h₂, linarith, },
  
  have h₄₉₆ : f (-1465) = -1468,
  { apply h₂, linarith, },
  
  have h₄₉₇ : f (-1470) = -1473,
  { apply h₂, linarith, },
  
  have h₄₉₈ : f (-1475) = -1478,
  { apply h₂, linarith, },
  
  have h₄₉₉ : f (-1480) = -1483,
  { apply h₂, linarith, },
  
  have h₅₀₀ : f (-1485) = -1488,
  { apply h₂, linarith, },
  
  have h₅₀₁ : f (-1490) = -1493,
  { apply h₂, linarith, },
  
  have h₅₀₂ : f (-1495) = -1498,
  { apply h₂, linarith, },
  
  have h₅₀₃ : f (-1500) = -1503,
  { apply h₂, linarith, },
  
  have h₅₀₄ : f (-1505) = -1508,
  { apply h₂, linarith, },
  
  have h₅₀₅ : f (-1510) = -1513,
  { apply h₂, linarith, },
  
  have h₅₀₆ : f (-1515) = -1518,
  { apply h₂, linarith, },
  
  have h₅₀₇ : f (-1520) = -1523,
  { apply h₂, linarith, },
  
  have h₅₀₈ : f (-1525) = -1528,
  { apply h₂, linarith, },
  
  have h₅₀₉ : f (-1530) = -1533,
  { apply h₂, linarith, },
  
  have h₅₁₀ : f (-1535) = -1538,
  { apply h₂, linarith, },
  
  have h₅₁₁ : f (-1540) = -1543,
  { apply h₂, linarith, },
  
  have h₅₁₂ : f (-1545) = -1548,
  { apply h₂, linarith, },
  
  have h₅₁₃ : f (-1550) = -1553,
  { apply h₂, linarith, },
  
  have h₅₁₄ : f (-1555) = -1558,
  { apply h₂, linarith, },
  
  have h₅₁₅ : f (-1560) = -1563,
  { apply h₂, linarith, },
  
  have h₅₁₆ : f (-1565) = -1568,
  { apply h₂, linarith, },
  
  have h₅₁₇ : f (-1570) = -1573,
  { apply h₂, linarith, },
  
  have h₅₁₈ : f (-1575) = -1578,
  { apply h₂, linarith, },
  
  have h₅₁₉ : f (-1580) = -1583,
  { apply h₂, linarith, },
  
  have h₅₂₀ : f (-1585) = -1588,
  { apply h₂, linarith, },
  
  have h₅₂₁ : f (-1590) = -1593,
  { apply h₂, linarith, },
  
  have h₅₂₂ : f (-1595) = -1598,
  { apply h₂, linarith, },
  
  have h₅₂₃ : f (-1600) = -1603,
  { apply h₂, linarith, },
  
  have h₅₂₄ : f (-1605) = -1608,
  { apply h₂, linarith, },
  
  have h₅₂₅ : f (-1610) = -1613,
  { apply h₂, linarith, },
  
  have h₅₂₆ : f (-1615) = -1618,
  { apply h₂, linarith, },
  
  have h₅₂₇ : f (-1620) = -1623,
  { apply h₂, linarith, },
  
  have h₅₂₈ : f (-1625) = -1628,
  { apply h₂, linarith, },
  
  have h₅₂₉ : f (-1630) = -1633,
  { apply h₂, linarith, },
  
  have h₅₃₀ : f (-1635) = -1638,
  { apply h₂, linarith, },
  
  have h₅₃₁ : f (-1640) = -1643,
  { apply h₂, linarith, },
  
  have h₅₃₂ : f (-1645) = -1648,
  { apply h₂, linarith, },
  
  have h₅₃₃ : f (-1650) = -1653,
  { apply h₂, linarith, },
  
  have h₅₃₄ : f (-1655) = -1658,
  { apply h₂, linarith, },
  
  have h₅₃₅ : f (-1660) = -1663,
  { apply h₂, linarith, },
  
  have h₅₃₆ : f (-1665) = -1668,
  { apply h₂, linarith, },
  
  have h₅₃₇ : f (-1670) = -1673,
  { apply h₂, linarith, },
  
  have h₅₃₈ : f (-1675) = -1678,
  { apply h₂, linarith, },
  
  have h₅₃₉ : f (-1680) = -1683,
  { apply h₂, linarith, },
  
  have h₅₄₀ : f (-1685) = -1688,
  { apply h₂, linarith, },
  
  have h₅₄₁ : f (-1690) = -1693,
  { apply h₂, linarith, },
  
  have h₅₄₂ : f (-1695) = -1698,
  { apply h₂, linarith, },
  
  have h₅₄₃ : f (-1700) = -1703,
  { apply h₂, linarith, },
  
  have h₅₄₄ : f (-1705) = -1708,
  { apply h₂, linarith, },
  
  have h₅₄₅ : f (-1710) = -1713,
  { apply h₂, linarith, },
  
  have h₅₄₆ : f (-1715) = -1718,
  { apply h₂, linarith, },
  
  have h₅₄₇ : f (-1720) = -1723,
  { apply h₂, linarith, },
  
  have h₅₄₈ : f (-1725) = -1728,
  { apply h₂, linarith, },
  
  have h₅₄₉ : f (-1730) = -1733,
  { apply h₂, linarith, },
  
  have h₅₅₀ : f (-1735) = -1738,
  { apply h₂, linarith, },
  
  have h₅₅₁ : f (-1740) = -1743,
  { apply h₂, linarith, },
  
  have h₅₅₂ : f (-1745) = -1748,
  { apply h₂, linarith, },
  
  have h₅₅₃ : f (-1750