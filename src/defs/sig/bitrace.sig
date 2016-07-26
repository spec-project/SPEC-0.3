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
#include "uni.sig".
#include "intruder.sig".
#include "obsthy.sig".

#kind bt_pair type.

#type in      (tm -> tm -> bt_pair).
#type out     (tm -> tm -> bt_pair).

#type mem_bitrace    (tm -> tm -> list bt_pair -> o).
#type pbitrace	     (list bt_pair -> o).
#type print_bitrace  (list bt_pair -> o).

#type get_var_bt     (list bt_pair -> list tm -> list tm -> o).

#type bitrace_vars   (list bt_pair -> list tm -> o).

#type prefix	     (tm -> list bt_pair -> list bt_pair -> o).

#type bt2thy	     (list bt_pair -> list thy_pair -> o).
 
#type fun_CS1	(list tm -> list bt_pair -> list sub_pair -> list sub_pair -> o).
 
#type fun_CS2	(list tm -> list bt_pair -> list sub_pair -> list sub_pair -> o).


#type bitrace_cst     (num -> list bt_pair -> list tm -> list constraint -> o).


#type fun_RC1 (list bt_pair -> constraint -> 
               list sub_pair -> list sub_pair -> o).


#type fun_RC2 (list bt_pair -> constraint -> 
               list sub_pair -> list sub_pair -> o).

#type fun_RS1 (list bt_pair -> list sub_pair -> list sub_pair ->
               list sub_pair -> list sub_pair -> o).

#type fun_RS2 (list bt_pair -> list sub_pair -> list sub_pair ->
               list sub_pair -> list sub_pair -> o).

#type apply_subst_bt (list sub_pair -> list sub_pair -> list bt_pair ->
                      list bt_pair -> o).

#type bt_consistent_iter (list bt_pair -> list thy_pair -> list bt_pair -> o).

#type bt_consistent (list bt_pair -> o).
