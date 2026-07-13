module jt51_mod_sva (
    input logic alg_I,
    input logic alg_hot,
    input logic c1_enters,
    input logic c2_enters,
    input logic m1_enters,
    input logic m2_enters,
    input logic use_internal_x,
    input logic use_internal_y,
    input logic use_prev1,
    input logic use_prev2,
    input logic use_prevprev1,
    input logic b0xx,
    input logic clk_in_19,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic d4,
    input logic d5,
    input logic d6,
    input logic d7,
    input logic h1,
    input logic h10,
    input logic h2,
    input logic h20,
    input logic h4,
    input logic h40,
    input logic h8,
    input logic h80,
    input logic hx
);

property ClockSynceotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd0 ) |-> ( alg_hot ) == 8'h1 ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_19) ( alg_I ) == ( 3'd1 ) |-> ( alg_hot ) == 8'h2 ; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_19) ( alg_I ) == ( 3'd2 ) |-> ( alg_hot ) == 8'h4 ; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_19) ( alg_I ) == ( 3'd3 ) |-> ( alg_hot ) == 8'h8 ; endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_19) ( alg_I ) == ( 3'd4 ) |-> ( alg_hot ) == 8'h10 ; endproperty
assert property (SyncIneotid_4);

property SyncIneotid_5; @(posedge clk_in_19) ( alg_I ) == ( 3'd5 ) |-> ( alg_hot ) == 8'h20 ; endproperty
assert property (SyncIneotid_5);

property SyncIneotid_6; @(posedge clk_in_19) ( alg_I ) == ( 3'd6 ) |-> ( alg_hot ) == 8'h40 ; endproperty
assert property (SyncIneotid_6);

property SyncIneotid_7; @(posedge clk_in_19) ( alg_I ) == ( 3'd7 ) |-> ( alg_hot ) == 8'h80 ; endproperty
assert property (SyncIneotid_7);

property SyncSafeeotid; @(posedge clk_in_19) ( alg_I ) != 3'b0xx  |-> ( alg_hot ) != 8'hx ; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_in_19) (  use_prevprev1  ) == (  m1_enters  |  ( m2_enters  & alg_hot [ 5 ] ) ) ; endproperty
assert property (SyncSafeeotid_2);

property SyncSafeeotid_3; @(posedge clk_in_19) (  use_prev2  ) == (  ( m2_enters  &  (  |  alg_hot [ 2 : 0 ]  ) )  |  ( c2_enters  &  alg_hot [ 3 ] )  ) ; endproperty
assert property (SyncSafeeotid_3);

property SyncSafeeotid_4; @(posedge clk_in_19) (  use_internal_x  ) == (  c2_enters  &  alg_hot [ 2 ]  ) ; endproperty
assert property (SyncSafeeotid_4);

property SyncSafeeotid_5; @(posedge clk_in_19) (  use_internal_y  ) == (  c2_enters  &  (  |  { alg_hot [ 4 : 3 ] , alg_hot [ 1 : 0 ]  }  )  ) ; endproperty
assert property (SyncSafeeotid_5);

property SyncSafeeotid_6; @(posedge clk_in_19) (  use_prev1  ) == (  m1_enters  |  ( m2_enters  & alg_hot [ 1 ] )  |  ( c1_enters  &  (  |  { alg_hot [ 6 : 3 ] , alg_hot [ 0 ]  }  )  )  |  ( c2_enters  &  (  |  { alg_hot [ 5 ] , alg_hot [ 2 ]  }  )  )  ; endproperty
assert property (SyncSafeeotid_6);

endmodule