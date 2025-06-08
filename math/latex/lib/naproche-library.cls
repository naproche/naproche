\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{naproche-library}[2025/01/03 package naproche-library]
\LoadClass{article}

\RequirePackage{naproche}
\RequirePackage{xurl} % for proper linebreaks of IDs
\RequirePackage{titling}

\setbool{printid}{true}     % Print top-level section IDs on the document margin
\setbool{highlight}{true}   % Highlight definienda and components of symbolic expressions

\RequirePackage[right=6cm,left=3cm,bottom=3cm,marginparwidth=5cm]{geometry}

\RequirePackage[nobottomtitles]{titlesec}
\titlespacing*{\section}{0pt}{30pt}{0pt}
\titlespacing*{\subsection}{0pt}{30pt}{0pt}
\titlespacing*{\subsubsection}{0pt}{30pt}{0pt}


% Rendering a Library Archive
% ---------------------------

\RequirePackage{hyperref}
\hypersetup{
    colorlinks=true,
    linkcolor=blue,
    urlcolor=blue
}

\libinput[latex]{license}


% Class Options
% -------------

\DeclareOption{numberswithinsection}{%
    \counterwithin{theoremcount}{section}
}
\DeclareOption{numberswithinsubsection}{%
    \counterwithin{theoremcount}{subsection}
}
\DeclareOption*{\PackageWarning{naproche}{Unknown ‘\CurrentOption’}}
\ProcessOptions\relax
