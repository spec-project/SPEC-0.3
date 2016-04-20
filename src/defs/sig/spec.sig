%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SPEC                                                                     
% Copyright (C) 2011 Alwen Tiu                                             
%
% This program is free software; you can redistribute it and/or modify     
% it under the terms of the GNU General Public License as published by     
% the Free Software Foundation; either version 2 of the License, or        
% (at your option) any later version.                                      
%
% This program is distributed in the hope that it will be useful,          
% but WITHOUT ANY WARRANTY; without even the implied warranty of           
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            
% GNU General Public License for more details.                             
%
% You should have received a copy of the GNU General Public License        
% along with this code; if not, write to the Free Software Foundation,     
% Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

#include "bisim.sig".
#include "bisim2text.sig". 
#include "bisim2latex.sig".

#type agent_def (tm -> def_body -> o).

#type show_bisim (N -> o -> o).

#type save_bisim (F -> N -> o -> o).

#type appdef (def_body -> list tm -> proc -> o).
#type expand_defs (proc -> proc -> o).

#type has_args (def_body -> o -> o).

#type print_agent_def (o -> def_body -> o).

#type show_def (tm -> o).

#type free_names_term (tm -> list tm -> list tm -> o).

#type free_names_args (list tm -> list tm -> list tm -> o).

#type free_names_proc (proc -> list tm -> list tm -> o).
#type free_names_def (def_body -> list tm -> o).

#type check_def (tm -> o).
#type bisim_def (proc -> proc -> o).
