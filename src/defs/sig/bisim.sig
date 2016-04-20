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

#include "basic.sig".
#include "bitrace.sig".
#include "proc.sig". 


#type fun_RSRC1 (list bt_pair -> list tm -> list sub_pair -> constraint -> 
      		      list sub_pair -> list sub_pair -> list sub_pair -> o).

#type fun_RSRC2 (list bt_pair -> list tm -> list sub_pair -> constraint -> 
      		      list sub_pair -> list sub_pair -> list sub_pair -> o).

#kind refinement type.

#type conRefProc (list sub_pair -> list sub_pair -> action -> proc -> refinement). 
#type conRefAgent (list sub_pair -> list sub_pair -> action -> agent -> refinement). 
#type absRef ((name -> refinement) -> refinement).


#type ref1_cont (list bt_pair -> list tm -> continuation -> refinement -> o).

#type ref2_cont (list bt_pair -> list tm -> continuation -> refinement -> o).

#type check_consistency (list bt_pair -> list thy_pair -> list bt_pair -> o).

#type bisim_upto (list bt_pair -> proc -> proc -> o).
#type bisimTau1 (list bt_pair -> proc -> refinement -> o).
#type bisimTau2 (list bt_pair -> proc -> refinement -> o).

#type bisimAgent (list bt_pair -> list thy_pair -> agent -> agent -> o).
#type bisimAbs1 (list bt_pair -> proc -> refinement -> o).
#type bisimAbs2 (list bt_pair -> proc -> refinement -> o).

#type bisimCon1 (list bt_pair -> proc -> refinement -> o).
#type bisimCon2 (list bt_pair -> proc -> refinement -> o).

#type get_var_inp (bt_pair -> list tm -> list tm -> o).
#type closed_inp (bt_pair -> o).

#type trim_history (list tm -> list bt_pair -> list bt_pair -> o).

#type print_bisim (list bt_pair -> proc -> proc -> o).

#type bisim (list bt_pair -> proc -> proc -> o).

#type toplevel_bisim (list bt_pair -> proc -> proc -> o).

#kind configuration type.
