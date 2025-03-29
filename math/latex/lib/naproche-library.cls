\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{naproche-library}[2025/01/03 package naproche-library]
\LoadClass{article}

\RequirePackage{naproche}
\RequirePackage{xurl} % for proper linebreaks of IDs

\setbool{printid}{true}     % Print top-level section IDs on the document margin
\setbool{highlight}{true}   % Highlight definienda and components of symbolic expressions

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

\DeclareOption{numberswithinsection}{%
    \counterwithin{theoremcount}{section}
}
\DeclareOption{numberswithinsubsection}{%
    \counterwithin{theoremcount}{subsection}
}
\DeclareOption*{\PackageWarning{naproche}{Unknown ‘\CurrentOption’}}
\ProcessOptions\relax
