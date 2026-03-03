// SVA for up_down_counter
module udc_sva(input CLK, input UP_DOWN, input RESET, input EN, input [3:0] OUT);
  default clocking cb @ (posedge CLK); endclocking

  // Reset/hold/update semantics
  a_reset_sync: assert property (RESET |-> OUT==4'h0) else $error("UDC: OUT not 0 during RESET");
  a_hold:       assert property (!RESET && !EN |-> OUT == $past(OUT)) else $error("UDC: OUT changed while EN=0");
  a_inc:        assert property (!RESET && EN &&  UP_DOWN |-> OUT == $past(OUT)+4'd1) else $error("UDC: INC wrong");
  a_dec:        assert property (!RESET && EN && !UP_DOWN |-> OUT == $past(OUT)-4'd1) else $error("UDC: DEC wrong");
  a_change_en:  assert property (!RESET && !$isunknown($past(OUT)) && (OUT != $past(OUT)) |-> EN) else $error("UDC: OUT changed without EN");

  // Async reset edge
  always @(posedge RESET) assert (OUT==4'h0) else $error("UDC: OUT not 0 on RESET edge");

  // Coverage
  c_inc:       cover property (!RESET && EN &&  UP_DOWN);
  c_dec:       cover property (!RESET && EN && !UP_DOWN);
  c_wrap_up:   cover property (!RESET && EN &&  UP_DOWN && $past(OUT)==4'hF |-> OUT==4'h0);
  c_wrap_down: cover property (!RESET && EN && !UP_DOWN && $past(OUT)==4'h0 |-> OUT==4'hF);
  c_hold:      cover property (!RESET && !EN |-> OUT==$past(OUT));
  c_reset:     cover property (RESET);
endmodule

// SVA for top: mux/connectivity and multiplier
module top_sva(
  input CLK,
  input select,
  input [3:0] A,
  input [3:0] B,
  input [3:0] OUT1,
  input [7:0] OUT2,
  input [3:0] udc_OUT,
  input [3:0] bm_A,
  input [3:0] bm_B,
  input [7:0] bm_OUT
);
  default clocking cb @ (posedge CLK); endclocking

  // Connectivity
  a_out1_conn: assert property (OUT1 == udc_OUT) else $error("TOP: OUT1 not from UDC");
  a_out2_conn: assert property (OUT2 == bm_OUT)  else $error("TOP: OUT2 not from BM");

  // Mux into multiplier
  a_mux_sel1: assert property (select  |-> (bm_A==A && bm_B==B)) else $error("TOP: select=1 mapping wrong");
  a_mux_sel0: assert property (!select |-> (bm_A==B && bm_B==A)) else $error("TOP: select=0 mapping wrong");

  // Multiplier correctness and end-to-end product
  a_mul_correct:  assert property (bm_OUT == (bm_A * bm_B)) else $error("BM: OUT != A*B");
  a_e2e_product:  assert property (OUT2   == (A * B))       else $error("TOP: OUT2 != A*B");

  // Coverage
  c_sel1:        cover property (select);
  c_sel0:        cover property (!select);
  c_sel_rise:    cover property ($rose(select));
  c_sel_fall:    cover property ($fell(select));
  c_mul_zero:    cover property (bm_A==4'h0 || bm_B==4'h0);
  c_mul_max:     cover property (bm_A==4'hF && bm_B==4'hF);
endmodule

// Bind assertions
bind up_down_counter udc_sva u_udc_sva(
  .CLK(CLK),
  .UP_DOWN(UP_DOWN),
  .RESET(RESET),
  .EN(EN),
  .OUT(OUT)
);

bind top_module top_sva u_top_sva(
  .CLK(CLK),
  .select(select),
  .A(A),
  .B(B),
  .OUT1(OUT1),
  .OUT2(OUT2),
  .udc_OUT(udc.OUT),
  .bm_A(bm.A),
  .bm_B(bm.B),
  .bm_OUT(bm.OUT)
);