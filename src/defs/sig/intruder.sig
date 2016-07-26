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

#include "uni.sig".
#include "pprint.sig".

#kind constraint type.


#type dedl (list tm -> tm -> constraint). 
#type dedr (list tm -> tm -> constraint).


#type constraints_vars (list constraint -> list tm -> o).

#type apply (list sub_pair -> constraint -> constraint -> o).

#type apply_list (list sub_pair -> list constraint -> list constraint -> o).

#type solve_constraints (list tm -> list constraint -> list sub_pair -> o).

#type print_cst (constraint -> o).

#type print_list_cst (list constraint -> o).

