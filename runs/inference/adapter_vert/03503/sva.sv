property ClockSynceotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd0 ) |-> ( alg_hot ) == 8'h1 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd1 ) |-> ( alg_hot ) == 8'h2 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd2 ) |-> ( alg_hot ) == 8'h4 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd3 ) |-> ( alg_hot ) == 8'h8 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd4 ) |-> ( alg_hot ) == 8'h10 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd5 ) |-> ( alg_hot ) == 8'h20 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd6 ) |-> ( alg_hot ) == 8'h40 ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd7 ) |-> ( alg_hot ) == 8'h80 ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) ( alg_I ) != 3'b0xx  |-> ( alg_hot ) != 8'hx ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) (  use_prevprev1  ) == (  m1_enters  |  ( m2_enters  & alg_hot [ 5 ] ) ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) (  use_prev2  ) == (  ( m2_enters  &  (  |  alg_hot [ 2 : 0 ]  ) )  |  ( c2_enters  &  alg_hot [ 3 ] )  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) (  use_internal_x  ) == (  c2_enters  &  alg_hot [ 2 ]  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) (  use_internal_y  ) == (  c2_enters  &  (  |  { alg_hot [ 4 : 3 ] , alg_hot [ 1 : 0 ]  }  )  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_19) (  use_prev1  ) == (  m1_enters  |  ( m2_enters  & alg_hot [ 1 ] )  |  ( c1_enters  &  (  |  { alg_hot [ 6 : 3 ] , alg_hot [ 0 ]  }  )  )  |  ( c2_enters  &  (  |  { alg_hot [ 5 ] , alg_hot [ 2 ]  }  )  )  ; endproperty 
 
 