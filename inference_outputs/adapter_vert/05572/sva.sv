property ResetSynceotid; @(negedge clk_reset_19) (blank) |-> s7 == 7'b0111111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (blank) &&  (  ! (  minus  )  ) |-> s7 == 7'b0000110 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  minus  ) |-> s7 == 7'b1011011 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  minus  ) &&  (  ! (  blank  )  ) |-> s7 == 7'b1001111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  == 4'h0 )  ) |-> s7 == 7'b1100110 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  == 4'h1 )  ) |-> s7 == 7'b1101101 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  == 4'h2 )  ) |-> s7 == 7'b1111101 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  == 4'h3 )  ) |-> s7 == 7'b0000111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  == 4'h4 )  ) |-> s7 == 7'b1100110 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  == 4'h5 )  ) |-> s7 == 7'b1101101 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  == 4'h6 )  ) |-> s7 == 7'b1111101 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  == 4'h7 )  ) |-> s7 == 7'b0000111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  == 4'h8 )  ) |-> s7 == 7'b1100110 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  == 4'h9 )  ) |-> s7 == 7'b1101111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  == 4'hA )  ) |-> s7 == 7'b1110111 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  != 4'hA )  &&  (  value  == 4'hB )  ) |-> s7 == 7'b1111100 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  != 4'hA )  &&  (  value  != 4'hB )  &&  (  value  == 4'hC )  ) |-> s7 == 7'b0111001 ; endproperty 
 
 property ResetSynceotid; @(