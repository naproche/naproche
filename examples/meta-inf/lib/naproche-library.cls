\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{naproche-library}[2025/01/03 package naproche-library]
\LoadClass{article}

\RequirePackage{naproche}

\setbool{printid}{true} % Print top-level section IDs on the document margin

\RequirePackage{stex-highlighting}
\newbool{emph}
\setbool{emph}{false}
\colorlet{emphcolor}{violet}
\let\oldemph\emph
\renewcommand\emph[1]{\setbool{emph}{true}\ifbool{forthel}{\textcolor{emphcolor}{\itshape#1}}{\oldemph{#1}}\setbool{emph}{false}}
\renewcommand{\varemph}[1]{\ifbool{emph}{\textcolor{emphcolor}{#1}}{\textcolor{teal}{#1}}}

\RequirePackage[right=6cm,left=3cm,bottom=3cm,marginparwidth=5cm]{geometry}

\RequirePackage{fancyhdr}
\renewcommand{\sectionmark}[1]{\markboth{#1}{}} 
\def\libarchive{}
\pagestyle{fancy}
\fancyhead[L]{\libarchive}
\fancyhead[C]{\nouppercase\leftmark}  % section title
\fancyhead[R]{\thepage}               % page number
\fancyfoot[C]{}                       % No page number in footer

\RequirePackage[nobottomtitles]{titlesec}
\titlespacing*{\section}{0pt}{30pt}{0pt}
\titlespacing*{\subsection}{0pt}{30pt}{0pt}
\titlespacing*{\subsubsection}{0pt}{30pt}{0pt}
