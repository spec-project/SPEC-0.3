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

#kind thy_pair type.

#type mp (tm -> tm -> thy_pair).

#type split_thy (list thy_pair -> list tm -> list tm -> o).

#type apply_subst_thy (list sub_pair -> list sub_pair -> list thy_pair
                       -> list thy_pair -> o).

#type print_thy (list thy_pair -> o).

#type deduce_r (list thy_pair -> tm -> tm -> o).

#type deduce_inv_r (list thy_pair -> tm -> tm -> o).

#type reduce (list thy_pair -> list thy_pair -> o).


#type thy_consistent (list thy_pair -> o).
#type thy_red_consistent (list thy_pair -> o).
