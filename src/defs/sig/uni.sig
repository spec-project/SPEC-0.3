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
#include "spi.sig". 

#kind tm_type type.

% message types
#type nm_type	tm_type.
#type ct_type 	tm_type.
#type var_type 	tm_type. 
#type pr_type	tm_type.
#type en_type	tm_type.
#type hs_type	tm_type.
#type aen_type	tm_type.
#type pub_type	tm_type.
#type sign_type	tm_type.
#type vk_type	tm_type.

% substitutions
#kind sub_pair type. % substitution pair

#type sub (tm -> tm -> sub_pair). 


#type closed (tm -> o).

#type get_var (tm -> list tm -> list tm -> o).

#type msg_type (tm -> tm_type -> o).

#type free (tm -> tm -> o).

#type not_free (tm -> tm -> o).

#type simp_cp (tm -> tm -> o).

#type copyterm (list sub_pair -> tm -> tm -> o).

#type id_subst (list tm -> list sub_pair -> o). 

#type copylist (list sub_pair -> list tm -> list tm -> o).

#type compose  (list tm -> list sub_pair -> list sub_pair -> list sub_pair -> o).

#type unify    (list sub_pair -> tm -> tm -> list tm -> list sub_pair -> o).

#type unify_list (list tm -> list tm ->  tm -> list sub_pair -> o).