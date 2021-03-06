% -*-Latex-*-
%\documentclass[a4paper,landscape]{slides}
\documentclass[colorhighlight,coloremph]{beamer}
\usetheme{boxes}
\usepackage{color,soul}
\usepackage{graphicx}
%%\usepackage[pdftex]{graphicx}
\usepackage{asymptote}
\usepackage{amsmath}
%% packages for unicode
\usepackage{amssymb}
%% \usepackage{bbm}
%%\usepackage[greek,english]{babel}
\usepackage[english]{babel}

%% unicode translation
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
%%\usepackage{autofe}
%%\usepackage{fancyvrb}

%include slides.fmt

\input{macros.TeX}

\renewcommand{\hscodestyle}{%
   \setlength\leftskip{1em}%
   \small
}

%%\fvset{xleftmargin=0.0} %%\parindent}

\addheadbox{section}{
  \quad \tiny
  Formalizing reachability, viability and avoidability in the context of
  SDPs
  \ $\rightarrow$ \
  \color{blue} \insertsection
}
%\addfootbox{section}{\quad \tiny Modelling Strategy Seminar, PIK, June
%  2012}
\title{Formalizing reachability, viability and avoidability in the
  context of sequential decision problems}

\author{Nicola Botta}

\begin{document}
\date{}
\frame{\maketitle}

%% -------------------------------------------------------------------

\section{Outline}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Outline}
%
\begin{itemize}
\vspace{0.3\normalbaselineskip}
\item Why formalizing what?
\vspace{0.3\normalbaselineskip}
\item Minimal goals
\vspace{0.3\normalbaselineskip}
\item Sequential decision problems
\vspace{0.3\normalbaselineskip}
\item Reachability, viability and avoidability
\vspace{0.3\normalbaselineskip}
\item Decision procedures
\vspace{0.3\normalbaselineskip}
\item Wrap-up
\end{itemize}
\vfill
%
\end{frame}


%% -------------------------------------------------------------------

\section{Why formalizing what?}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Why formalizing what?}
%
\begin{itemize}
  \vspace{0.3\normalbaselineskip}
  \item<1-> \emph{International emissions trading: Good or bad?},
    Holtsmark \& Sommervoll, 2012: ``[\ldots] we find that an agreement
    with international emissions trading leads to \textcolor<2-3>{red}{increased emissions}
    and \textcolor<2-3>{red}{reduced efficiency}.''
  \vspace{0.3\normalbaselineskip}
  \item<1-> \emph{The case for international emission trade in the
    absence of cooperative climate policy}, Carbone et al., 2009:
    ``[\ldots] we find that emission trade agreements \textcolor<3>{green}{can be effective}
    [\ldots]''
  \vspace{0.3\normalbaselineskip}
  \item<4-> \emph{Confronting Climate Change: \textcolor{red}{Avoiding the Unmanageable
    and Managing the Unavoidable}}, P. Raven, R. Bierbaum, J. Holdren,
    UN-Sigma Xi Climate Change Report, 2007.
\end{itemize}
%
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Why formalizing what?}
%
Some notion of avoidability is implicit in the WG3\_IPCC\_AR5\_2014
definitions of
\begin{itemize}
  \vspace{0.3\normalbaselineskip}
  \item<1-> \emph{mitigation}: ``A human intervention to reduce the
    sources or enhance the sinks of greenhouse gases'' \onslide<2->{$\Rightarrow$
    \textcolor{red}{avoid high atmospheric GHG concentrations}}
  \vspace{0.3\normalbaselineskip}
  \item<3-> \emph{adaptation}: ``The process of adjustment to actual or
    expected climate and its effects \dots to moderate harm or exploit
    beneficial opportunities'' \onslide<4->{$\Rightarrow$ \textcolor{red}{avoid
      too much harm, realize beneficial opportunities}}
\end{itemize}
%
\vspace{0.3\normalbaselineskip} \onslide<5->{But what does it mean (for
  atmospheric GHG concentrations) to be \emph{avoidable}?}
%
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Why formalizing what?}
%
\begin{figure}[h]
  \includegraphics[scale=0.4]{schellnhuber.pdf}
\end{figure}
\begin{tabular}{p{0.9\textwidth}}
``Die Rolle der Klimaforschung bleibt weiterhin, die Problemfakten auf
den Tisch zu knallen und Optionen f\"ur geeignete L\"osungswege zu
identifizieren.'' \\
\end{tabular}

\hfill H.-J. Schellnhuber in \emph{Frankfurter Allgemeine} from 2012-06-19 \\
%
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Why formalizing what?}
%
But how can we produce ``hard facts'' if the notions used to phrase
specific, concrete problems are ambiguous, devoid of precise, well
established, meanings?
%
\end{frame}

%% -------------------------------------------------------------------

\section{Minimal goals}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Minimal goals}
%
\begin{itemize}
  \vspace{0.3\normalbaselineskip}
  \pause
  \item Explain what it means for future (possibly harmful) states to be
    avoidable [reachable, viable, \dots]
  \vspace{0.3\normalbaselineskip}
  \pause
  \item Explain under which conditions the question of whether future
    states are avoidable [reachable, viable, \dots] can be decided
\end{itemize}
\pause
Further questions, goals
\begin{itemize}
  \vspace{0.3\normalbaselineskip}
  \pause
  \item Can one exploit decidability to derive useful avoidability
    (levity?) measures?
  \vspace{0.3\normalbaselineskip}
  \pause
  \item Can one refine decidable notions of viability, avoidability to
    derive decidable notions (measures?) of sustainability,
    adaptability, resilience?
\end{itemize}
%
\end{frame}


%% -------------------------------------------------------------------

\section{Sequential decision problems (intuition)}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (intuition)} % show only the states for n+1

\pause
\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
    A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
    draw(A--B--C--D--A,blue);
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), white);
  draw(Circle((cx-1.5,cy-1.5),0.5), white);
  draw(Circle((cx+2,cy+2),0.5), white);
  draw(Circle((cx-0.2,cy+1.5),0.5), white);
  draw(Circle((cx+1.8,cy-1.2),0.5), white);
  draw(Circle((cx+1.8,cy-1.2),0.5), white);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), white);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,white);
    }
    }
  }
  label("n steps left", (x+17,y+2), white);
  for (int j = 5; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), white, EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{You are here\ldots} % show only the states for
                                % n+1 and fill the state we're in

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), white);
  draw(Circle((cx-1.5,cy-1.5),0.5), white);
  draw(Circle((cx+2,cy+2),0.5), white);
  draw(Circle((cx-0.2,cy+1.5),0.5), white);
  draw(Circle((cx+1.8,cy-1.2),0.5), white);
  draw(Circle((cx+1.8,cy-1.2),0.5), white);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), white);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,white);
    }
    }
  }
  label("n steps left", (x+17,y+2), white);
  for (int j = 5; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), white, EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{These are your options\ldots} % show only the states for
                                % n+1 and fill the state we're in and
                                % show the available controls

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  draw(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), white);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,white);
    }
    }
  }
  label("n steps left", (x+17,y+2), white);
  for (int j = 5; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), white, EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Pick one!} % show only the states for
                                % n+1 and fill the state we're in
                                % show the available controls and fill
                                % in a choice

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  fill(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), white);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,white);
    }
    }
  }
  label("n steps left", (x+17,y+2), white);
  for (int j = 5; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), white, EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Advance one step\ldots} % transition from n+1 to n

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  fill(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,blue);
    }
    }
  }
  label("n steps left", (x+17,y+2), black);
  for (int j = 2; j < 3; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), black,
    EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{\ldots collect rewards \ldots} % we are now in n and we
                                           % collect our reward

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         draw(A--B--C--D--A,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  fill(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
      if (i == 2) {
         fill (A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
    }
  }
  label("n steps left", (x+17,y+2), black);
  for (int j = 2; j < 3; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), black,
    EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{\ldots and go!} % only states at n steps left


\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), white);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         draw(A--B--C--D--A,white);
      } else {
         draw(A--B--C--D--A,white);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), white);
  fill(Circle((cx-1.5,cy-1.5),0.5), white);
  draw(Circle((cx+2,cy+2),0.5), white);
  draw(Circle((cx-0.2,cy+1.5),0.5), white);
  draw(Circle((cx+1.8,cy-1.2),0.5), white);
  draw(Circle((cx-2.1,cy+1.2),0.5), white);
  label("n+1 steps left", (x+17,2), white);
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
      if (i == 2) {
         fill (A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
    }
  }
  label("n steps left", (x+17,y+2), black);
  for (int j = 2; j < 3; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), white,
    EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{General sequential decision problems (intuition)} % non-deterministic transition

\vfill
This intuition is a bit too simplistic \dots

\pause
\vfill
\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  fill(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,blue);
    }
    }
  }
  label("n steps left", (x+17,y+2), black);
  for (int j = 1; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), red,
    EndArrow);
  }


\end{asy}
\end{figure}

\vfill

\end{frame}

%% -------------------------------------------------------------------

\section{Sequential decision problems}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Notation (language)}

\vfill
\begin{figure}
\begin{tabular}{||l||l||}
\hline
   Idris                 & set theory, logic
\\ \hline
   |A : Type|            & $A$ is a set
\\ |a : A|               & $a \in A$
\\ |f : A -> B|          & $f : A \rightarrow B$
\\ |b = f a|             & $b = f(a)$
\\ |(a + b) * c|         & $(a + b) * c$
\\ |P : Type|            & $P$ is a predicate
\\ |p : P|               & $p$ is a proof of $P$
\\ |p : P -> Void|       & $p$ is a proof of $\neg P$
\\ |P -> Q|              & $P$ implies $Q$
\\ |P : A -> Type|       & $P$ is a predicate on $A$
\\ |pa : P a|            & $pa$ is a proof of $P(a)$
\\ |(a : A ** P a)|      & there exists an $a \in A$ such that $P(a)$ holds
\\ |(a : A) -> P a|      & forall $a \in A$, $P(a)$ holds
\\ \hline
\end{tabular}
  \caption{Curry-Howard correspondence relating Idris and set theory, logic.}
\end{figure}

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (basic notions)}

\begin{figure}[h]
 \begin{asy}
  include graph;
  size(11cm);
  int o = 1;
  int l = 8;
  int h = 4;
  pair A, B, C, D;
  int x = 0;
  real[] midxs1;
  real[] midys1;
  real[] midxs2;
  real[] midys2;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs1.push(x + l/2);
    midys1.push(0);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
      }
    } else
    {
      A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
      if (i == 1) {
         fill(A--B--C--D--cycle,blue);
      } else {
         draw(A--B--C--D--A,blue);
      }
    }
  }
  int cx = l+o+floor(l/2);
  int cy = h + h + h;
  int cr = floor(h);
  draw(Circle((cx,cy),cr), blue);
  fill(Circle((cx-1.5,cy-1.5),0.5), green);
  draw(Circle((cx+2,cy+2),0.5), yellow);
  draw(Circle((cx-0.2,cy+1.5),0.5), brown);
  draw(Circle((cx+1.8,cy-1.2),0.5), red);
  draw(Circle((cx-2.1,cy+1.2),0.5), black);
  label("n+1 steps left", (x+17,2));
  int y = -15;
  for (int i = 0; i < 6; ++i)
  {
    x = i * (l + o);
    midxs2.push(x + l/2);
    midys2.push(y+h);
    if (i == 3)
    {
      real a = (l+2*o)/3;
      for (int j = 1; j < 4; ++j)
      {
        draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
      }
    } else
    {
    A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
    if (i == 0 || i == 5)
    {
    draw(A--B--C--D--A,white);
    } else
    {
    draw(A--B--C--D--A,blue);
    }
    }
  }
  label("n steps left", (x+17,y+2), black);
  for (int j = 1; j < 5; ++j)
  {
    draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), red,
    EndArrow);
  }

\end{asy}
\end{figure}

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (basic notions)}

\vfill
At each decision step, a set of possible states:

> X     :  (t : Nat) -> Type

\pause
\vfill
At each decision step and for each state, a set of options

> Y     :  (t : Nat) -> (x : X t) -> Type

\pause
\vfill
A transition function

> step  :  (t : Nat) -> (x : X t) -> (y : Y t x) -> redM (X (redS t))

\pause
\vfill
What are |M| and |S|?

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (uncertainties)}

\vfill
\vspace{0.6\normalbaselineskip}
|S t| is just the successor of |t|:

%include gray.lhs
> data Nat : Type where
>   Z  :  Nat
>   S  :  Nat -> Nat
%include black.lhs

\pause
%\vspace{0.3\normalbaselineskip}
\vfill
|M : Type -> Type| represents the uncertainties of the problem:
\begin{itemize}
\vspace{0.3\normalbaselineskip}
\item deterministic problems: |M = Id|
\vspace{0.3\normalbaselineskip}
\item non-deterministic problems: |M = List|
\vspace{0.3\normalbaselineskip}
\item stochastic problems: |M = Prob|
\end{itemize}

\pause
\vfill
%\vspace{0.3\normalbaselineskip}

%include gray.lhs
> data Prob : Type -> Type where
>   mkProb  :  (as : Vect n a) -> (ps : Vect n Float) ->
>              sum ps = 1.0 -> Prob a
%include black.lhs

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (container monad)}

\vfill
Formally, |M| is a container monad, that is |M| is a monad:

> fmap  :  (a -> b) -> M a -> M b
> ret   :  a -> M a
> bind  :  M a -> (a -> M b) -> M b
> join  :  M (M a) -> M a

\vfill
%include gray.lhs
> functorSpec1  :  fmap . id = id
> functorSpec2  :  fmap (f . g) = (fmap f) . (fmap g)
>
>
> monadSpec1  :  (fmap f) . ret = ret . f
> monadSpec2  :  bind (ret a) f = f a
> monadSpec3  :  bind ma ret = ma
> monadSpec4  :  {f : a -> M b} -> {g : b -> M c} ->
>                bind (bind ma f) g = bind ma (\ x => bind (f x) g)
> monadSpec5  :  join mma = bind mma id
%include black.lhs

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (container monad)}

\vfill
and |M| is a container:

> Elem  :  a -> M a -> Type
>
> All   :  (a -> Type) -> M a -> Type

> containerSpec1  :  a `Elem` (ret a)
>
> containerSpec2  :  a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)
>
> containerSpec3  :  All p ma -> a `Elem` ma -> p a

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Sequential decision problems (basic notions)}

\vfill
Thus, a concrete sequential decision problem is defined (up to the
rewards) in terms of 4 entities: |X|, |Y|, |M| and |step|

> X     :  (t : Nat) -> Type

> Y     :  (t : Nat) -> (x : X t) -> Type

> M     :  Type -> Type

> step  :  (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))

\pause
\vfill
We formalize reachability, viability and avoidability in terms of
these notions

\vfill
\end{frame}

%% -------------------------------------------------------------------

\section{Reachability, viability and avoidability}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Reachability and viability (intuition)}

\vfill
\begin{figure}
%
 \hspace*{-0.5cm}
%
 \begin{asy}
  size(6cm);
  include graph;
  string[] xs = {"a","b","c","d","e"};
  string[] path = {"b","c","d","e","e","d","c","d"};
  string[] cr   = {"7","2","1","4","7","8","8","7"};
  int nc = xs.length;
  int nt = path.length;
  real x0 = 0.0;
  real t0 = 0.0;
  real dx = 0.1;
  real dt = 0.1;
  real x;
  real t;
  pair A, B, C, D;
  defaultpen(2);
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    label(xs[j], position=(x+dx/2,t0-1.5*dt), align=N);
  }
  for (int i = 0; i < nt; ++i) {
    x = x0;
    t = t0 + i * dt;
    label((string) i, (x-dx,t+dt/2));
    for (int j = 0; j < nc; ++j) {
      x = x0 + j * dx;
      A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
      if (i == 3 && j < nc - 1) fill(A--B--C--D--A--cycle);
      if (i == 6 && j > nc - 3) fill(A--B--C--D--A--cycle);
      draw(A--B--C--D--A, grey);
    }
  }
  x = x0;
  t = t0 + (0 + nt) * dt + dt/2;
  label("...", (x-dx,t+dt/2));
  label("...", (x+nc*dx/2,t+dt/2));
  x = x0;
  t = t0 + (1 + nt) * dt + dt;
  label("n", (x-dx,t+dt/2));
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
    draw(A--B--C--D--A, grey);
  }
  int steps = 7;
  for (int i = 0; i < steps - 1; ++i) {
    t = t0 + i * dt;
    int j = search(xs,path[i]);
    x = x0 + j * dx;
    label(cr[i], (x+dx/2,t+dt/2), lightred);
  }
  if (steps > 0) {
    t = t0 + (steps - 1) * dt;
    int j = search(xs,path[steps - 1]);
    x = x0 + j * dx;
    label(cr[steps - 1], (x+dx/2,t+dt/2), lightred);
  }
  for (int i = 0; i < steps; ++i) {
    t = t0 + i * dt;
    int j = search(xs,path[i]);
    x = x0 + j * dx;
    A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
    draw(A--B--C--D--A, lightred);
  }
  t = t0 + steps * dt;
  int j = search(xs,path[steps]);
  x = x0 + j * dx;
  A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
  label("?", (x+dx/2,t+dt/2), red);
  draw(A--B--C--D--A, red);
 \end{asy}
%
 \hspace*{0.5cm}
%
 \begin{asy}
  size(6cm);
  include graph;
  string[] xs = {"a","b","c","d","e"};
  string[] path = {"b","c","d","e","e","d","c","d"};
  string[] cr = {"7","2","1","4","7","8","8","7"};
  int nc = xs.length;
  int nt = path.length;
  real x0 = 0.0;
  real t0 = 0.0;
  real dx = 0.1;
  real dt = 0.1;
  real x;
  real t;
  pair A, B, C, D;
  defaultpen(2);
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    label(xs[j], position=(x+dx/2,t0-1.5*dt), align=N);
  }
  for (int i = 0; i < nt; ++i) {
    x = x0;
    t = t0 + i * dt;
    label((string) i, (x-dx,t+dt/2));
    for (int j = 0; j < nc; ++j) {
      x = x0 + j * dx;
      A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
      if (i == 0 && j < nc - 1 - 3) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 1 && j < nc - 1 - 2) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 2 && j < nc - 1 - 1) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 3 && j < nc - 1) fill(A--B--C--D--A--cycle);
      if (i == 5 && j > nc - 3 + 1) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 6 && j > nc - 3) fill(A--B--C--D--A--cycle);
      draw(A--B--C--D--A, grey);
    }
  }
  x = x0;
  t = t0 + (0 + nt) * dt + dt/2;
  label("...", (x-dx,t+dt/2));
  label("...", (x+nc*dx/2,t+dt/2));
  x = x0;
  t = t0 + (1 + nt) * dt + dt;
  label("n", (x-dx,t+dt/2));
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
    draw(A--B--C--D--A, grey);
  }
 \end{asy}
%
 \hspace*{0.5cm}
%
 \begin{asy}
  size(6cm);
  include graph;
  string[] xs = {"a","b","c","d","e"};
  string[] path = {"b","c","d","d","d","c","b","a"};
  string[] cr = {"1","3","5","4","7","8","8","7"};
  int nc = xs.length;
  int nt = path.length;
  real x0 = 0.0;
  real t0 = 0.0;
  real dx = 0.1;
  real dt = 0.1;
  real x;
  real t;
  pair A, B, C, D;
  defaultpen(2);
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    label(xs[j], position=(x+dx/2,t0-1.5*dt), align=N);
  }
  for (int i = 0; i < nt; ++i) {
    x = x0;
    t = t0 + i * dt;
    label((string) i, (x-dx,t+dt/2));
    for (int j = 0; j < nc; ++j) {
      x = x0 + j * dx;
      A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
      if (i == 6 && j < nc - 1 - 3) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 5 && j < nc - 1 - 2) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 4 && j < nc - 1 - 1) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 3 && j < nc - 1) fill(A--B--C--D--A--cycle);
      if (i == 7 && j > nc - 3 + 1) fill(A--B--C--D--A--cycle, lightgrey);
      if (i == 6 && j > nc - 3) fill(A--B--C--D--A--cycle);
      draw(A--B--C--D--A, grey);
    }
  }
  x = x0;
  t = t0 + (0 + nt) * dt + dt/2;
  label("...", (x-dx,t+dt/2));
  label("...", (x+nc*dx/2,t+dt/2));
  x = x0;
  t = t0 + (1 + nt) * dt + dt;
  label("n", (x-dx,t+dt/2));
  for (int j = 0; j < nc; ++j) {
    x = x0 + j * dx;
    A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
    draw(A--B--C--D--A, grey);
  }
 \end{asy}
\caption{\small Possible evolution starting from $b$ (left), states with
 limited viability (middle) and unreachable states (right). \label{figure:one}}
\end{figure}

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Predecessor relation, reachability and viability}

\vfill
\vspace{0.6\normalbaselineskip}
The (possible) predecessor relation:

> Pred : X t -> X (S t) -> Type
> Pred {t} x x'  =  (y : Y t x ** x' `Elem` (step t x y))

\pause
\vfill
reachability

> Reachable : X t' -> Type
> Reachable {t' = Z}   x'  =  Unit
> Reachable {t' = S t} x'  =  (x : X t ** (Reachable x, x `Pred` x'))

\pause
\vfill
and viability

> Viable : (n : Nat) -> X t -> Type
> Viable {t} !Z    x  =  Unit
> Viable {t} (S m) x  =  (y : Y t x ** All (Viable m) (step t x y))

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Avoidability (intuition)}

\vfill
\begin{itemize}
\vspace{0.3\normalbaselineskip}
\pause
\item The notion of avoidability is necessarily a relative one: whether
  a future state is avoidable or not, depends in general on an (actual
  or hypothetical) current state.
\vspace{0.3\normalbaselineskip}
\pause
\item Thus, avoidability is a relation between states. More precisely,
  it is a relation between states at a given time and states at some
  later times.
\vspace{0.3\normalbaselineskip}
\pause
\item We are interested in the avoidability of ``possible'' future
  states. Specifically, we are interested in the avoidability of states
  which are reachable from some given state.
\vspace{0.3\normalbaselineskip}
\pause
\item The notion of avoidability entails the notion of an alternative.
\end{itemize}

\vfill
\end{frame}


%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Avoidability}

\vfill
We are interested in the avoidability of states which are reachable from
some given state:

> ReachableFrom : X t'' -> X t -> Type
> ReachableFrom {t'' = Z}    {t} x'' x  =  (t = Z , x = x'')
> ReachableFrom {t'' = S t'} {t} x'' x  =
>   Either  (t = S t' , x = x'')
>           (x' : X t' ** (x' `ReachableFrom` x , x' `Pred` x''))

where

> data Either a b = Left a | Right b

\pause
\vfill
\textcolor{gray}{Proof of concept: show that}
%include gray.lhs
> reachableFromLemma  :  (x'' : X t'') -> (x : X t) ->
>                        x'' `ReachableFrom` x -> t'' `GTE` t
%include black.lhs

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Avoidability}

\vfill
The notion of avoidability entails the notion of an alternative state
|x''|. This has to fulfill three conditions:

> AvoidableFrom  :  (x' : X t') -> (x : X t) ->
>                   x' `ReachableFrom` x -> (m : Nat) -> Type
>
> AvoidableFrom {t'} x' x r m =
>   (x'' : X t' ** (x'' `ReachableFrom` x !,! (Viable m x'' !,! Not (x'' = x'))))

\pause
\vfill
Back to the minimal goals: under which conditions are reachability,
viability and avoidability decidable?

\vfill
\end{frame}

%% -------------------------------------------------------------------

\section{Decision procedures}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
For every type (predicate) |P : Type|, |Not P| is just a synonym for
|P -> Void|:

> Not : Type -> Type
> Not P = P -> Void

\pause
\vfill
A predicate |P : Type| is \emph{decidable} if one can compute either a
value |p : P| or a value of type |Not P|:

> Decidable : Type -> Type
> Decidable P = Either P (Not P)

\vfill
\end{frame}


%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
Thus, the question is under which conditions one can implement

< decReachable : (x : X t) -> Decidable (Reachable x)

< decViable : (n : Nat) -> (x : X t) -> Decidable (Viable n x)

> decAvoidableFrom  :  {t' : Nat} -> {t : Nat} ->
>                      (x' : X t') -> (x : X t) ->
>                      (r : x' `ReachableFrom` x) -> (n : Nat) ->
>                      Decidable (AvoidableFrom {t'} {t} x' x r n)

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
As one would expect, the conditions

> fX : (t : Nat) -> Finite (X t)

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)

> decElem  :  {t : Nat} -> (x : X t) -> (mx : M (X t)) ->
>             Decidable (x `Elem` mx)

> decAll  :  {t : Nat} -> (P : X t -> Type) -> ((x : X t) ->
>            Decidable (P x)) -> (mx : M (X t)) ->
>            Decidable (All P mx)

are sufficient for decidability.

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
The key lemma for implementing decision procedures for |Reachable|,
|Viable| and |AvoidableFrom| is intuitively obvious

> finiteDecidableLemma  :  {A : Type} ->
>                          {P : A -> Type} ->
>                          Finite A ->
>                          ((a : A) -> Decidable (P a)) ->
>                          Decidable (a : A ** P a)

\pause
but implementing |finiteDecidableLemma| is not trivial!

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
With |finiteDecidableLemma|, |fY| and decidability of |Elem| one
immediately has decidability of |Pred|

> decPred  :  {t : Nat} -> (x : X t) -> (x' : X (S t)) ->
>             Decidable (x `Pred` x')
>
> decPred {t} x x' = finiteDecidableLemma (fY t x) prf where
>   prf : (y : Y t x) -> Decidable (x' `Elem` (step t x y))
>   prf y = decElem x' (step t x y)

\pause
\vfill
Remember

< Pred {t} x x'  =  (y : Y t x ** x' `Elem` (step t x y))

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
and, with

> decPair : Decidable p -> Decidable q -> Decidable (p , q)

\vfill
decidability of |Reachable|:

> decReachable : {t' : Nat} -> (x' : X t') -> Decidable (Reachable x')
>
> decReachable {t' = Z}   x' = Left ()
>
> decReachable {t' = S t} x' = s1 where
>   s1  :  Decidable (x : X t ** (Reachable x, x `Pred` x'))
>   s1  =  finiteDecidableLemma
>          (fX t)
>          (\x => decPair (decReachable x) (decPred x x'))

\vfill
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}[fragile]
\frametitle{Decision procedures}

\vfill
Similarly, one can implement (prove) decidability of |Viable|:

> decViable  :  {t : Nat} -> (n : Nat) -> (x : X t) ->
>               Decidable (Viable n x)
>
> decViable {t}  Z    x = Left ()
>
> decViable {t} (S m) x = s3 where
>   s1    :  (y : Y t x) -> Decidable (All (Viable m) (step t x y))
>   s1 y  =  decAll (Viable m) (decViable m) (step t x y)
>   s2    :  Decidable (y : Y t x ** All (Viable m) (step t x y))
>   s2    =  finiteDecidableLemma (fY t x) s1
>   s3    :  Decidable (Viable (S m) x)
>   s3    =  s2

\vfill
\pause
Implementing a decision procedure for |AvoidableFrom| is a bit more
complicated but conceptually equivalent.

\vfill
\end{frame}

%% -------------------------------------------------------------------

\section{Wrap-up}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Wrap-up}
\vfill
\begin{itemize}
\vspace{0.3\normalbaselineskip}
\item<1-> It is not difficult to formalize viability, reachability and
  avoidability for a large class of decision problems.
\vspace{0.3\normalbaselineskip}
\item<2-> The specific aspects of a concrete decision problem are
  captured by four abstractions: |X|, |Y|, |M| and |step|.
\vspace{0.3\normalbaselineskip}
\item<3-> In particular, different kinds of uncertainty (for instance,
  of the models underlying |step|) are covered by |M|, a monadic
  container.
\vspace{0.3\normalbaselineskip}
\item<4-> For finite |X| and |Y| decision procedures for viability,
  reachability and avoidability can be derived rigorously.
\vspace{0.3\normalbaselineskip}
\item<5-> Decidable generic [viability, reachability, avoidability]
  notions are hopefully a good starting point for deriving decidable
  domain specific notions: sustainability, adaptability, resilience, \dots
\end{itemize}
\vfill
\end{frame}

%% -------------------------------------------------------------------

\section{Acknowledgments}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Acknowledgments}
\vfill
Contributors:

Patrik Jansson (Chalmers Univ. of Technology), Cezar Ionescu (Chalmers
Univ. of Technology), David Christiansen (IT University of Copenhagen),
Edwin Brady (University of St. Andrews), Matteo Acerbi, members of the
Cartesian Seminar at the Univ. of Potsdam

\pause
\vfill
These slides:

\url{https://github.com/nicolabotta/SeqDecProbs/tree/master/talks/2015.06.rd4_seminar}

\pause
\vfill
The code shown in these slides:

\url{https://github.com/nicolabotta/SeqDecProbs/blob/master/talks/2015.06.rd4_seminar/code/Theory.lidr}
\vfill
\end{frame}

%% -------------------------------------------------------------------

\end{document}
