// SVA checkers and binds for the given DUTs
// Focused, concise, high-signal-coverage

// ===================== register =====================
module register_sva #(parameter N=8)
(
  input clk,
  input [N-1:0] in,
  input         load,
  input         clear,
  input [N-1:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (clear);

  // Async clear drives zero immediately
  a_reg_async_clear: assert property (@(posedge clear) out == '0);

  // On load, next-cycle out == in (expected spec)
  a_reg_load:        assert property (load |=> out == $past(in));

  // When not loading, hold previous value (will catch bug in DUT)
  a_reg_hold:        assert property (!load |=> out == $past(out));

  // Basic coverage
  c_reg_clear: cover property (@(posedge clear) 1);
  c_reg_load:  cover property (load);
  c_reg_hold:  cover property (!load);
endmodule

bind register register_sva #(.N(N)) u_register_sva (.*);

// ===================== register_hl =====================
module register_hl_sva #(parameter N=16)
(
  input clk,
  input [N/2-1:0] inh,
  input [N/2-1:0] inl,
  input           loadh,
  input           loadl,
  input           clear,
  input [N-1:0]   out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (clear);

  // Async clear drives zero immediately
  a_rhl_async_clear: assert property (@(posedge clear) out == '0);

  // High/low half update on respective loads
  a_rhl_loadh: assert property (loadh |=> out[N-1      :N/2]   == $past(inh));
  a_rhl_loadl: assert property (loadl |=> out[N/2-1:0]         == $past(inl));

  // Hold behavior per half when not loaded
  a_rhl_holdh: assert property (!loadh |=> out[N-1      :N/2]  == $past(out[N-1      :N/2]));
  a_rhl_holdl: assert property (!loadl |=> out[N/2-1:0]        == $past(out[N/2-1:0]));

  // Both halves can update simultaneously
  a_rhl_both:  assert property (loadh && loadl |=> out == {$past(inh), $past(inl)});

  // Coverage
  c_rhl_both:  cover property (loadh && loadl);
  c_rhl_h_then_l: cover property (loadh ##1 loadl);
  c_rhl_l_then_h: cover property (loadl ##1 loadh);
endmodule

bind register_hl register_hl_sva #(.N(N)) u_register_hl_sva (.*);

// ===================== upcreg =====================
module upcreg_sva
(
  input        clk,
  input        reset,
  input        load_incr,
  input  [4:0] upc_next,
  input  [4:0] upc
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Async reset drives zero immediately
  a_upc_async_reset: assert property (@(posedge reset) upc == 5'b00000);

  // Reset dominates at clock edge (no disable)
  a_upc_reset_prio:  assert property (@(posedge clk) disable iff (1'b0) reset |-> upc == 5'b00000);

  // Load vs increment behavior
  a_upc_load:        assert property (load_incr     |=> upc == $past(upc_next));
  a_upc_incr:        assert property (!load_incr    |=> upc == $past(upc) + 5'd1);

  // Knownness after reset deasserted
  a_upc_known:       assert property (!$isunknown(upc));

  // Coverage: load, incr, wraparound
  c_upc_load:        cover property (load_incr);
  c_upc_incr:        cover property (!load_incr);
  c_upc_wrap:        cover property ($past(upc)==5'h1F && !load_incr |=> upc==5'h00);
endmodule

bind upcreg upcreg_sva u_upcreg_sva (.*);

// ===================== mux5 =====================
module mux5_sva
(
  input      d0, d1, d2, d3, d4,
  input [2:0] s,
  input       y
);
  // Combinational correctness (immediate assertions)
  always @* begin
    unique case (s)
      3'd0: assert (y == d0);
      3'd1: assert (y == d1);
      3'd2: assert (y == d2);
      3'd3: assert (y == d3);
      3'd4: assert (y == d4);
      default: assert (y == 1'b0);
    endcase
    if (!$isunknown({d0,d1,d2,d3,d4,s})) assert (!$isunknown(y));
  end

  // Simple functional coverage per select value
  always @* begin
    cover (s == 3'd0);
    cover (s == 3'd1);
    cover (s == 3'd2);
    cover (s == 3'd3);
    cover (s == 3'd4);
    cover (s >= 3'd5); // default branch
  end
endmodule

bind mux5 mux5_sva u_mux5_sva (.*);

// ===================== addsub =====================
module addsub_sva
(
  input  [7:0] dataa,
  input  [7:0] datab,
  input        add_sub,
  input  [7:0] result,
  input        clk
);
  // Combinational equivalence
  always @* begin
    assert (result == (add_sub ? (dataa + datab) : (dataa - datab)));
    if (!$isunknown({dataa, datab, add_sub})) assert (!$isunknown(result));
  end

  // Coverage: both modes seen
  c_add: cover property (@(posedge clk) add_sub);
  c_sub: cover property (@(posedge clk) !add_sub);
endmodule

bind addsub addsub_sva u_addsub_sva (.*);

// ===================== counter_down =====================
module counter_down_sva
(
  input        clk,
  input        reset,
  input        ena,
  input  [7:0] result
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Async reset to 7
  a_cnt_async_reset: assert property (@(posedge reset) result == 8'd7);

  // Reset dominates at clock edge (no disable)
  a_cnt_reset_prio:  assert property (@(posedge clk) disable iff (1'b0) reset |-> result == 8'd7);

  // Decrement when enabled, hold otherwise
  a_cnt_dec:         assert property (ena  |=> result == $past(result) - 8'd1);
  a_cnt_hold:        assert property (!ena |=> result == $past(result));

  // Wrap-around coverage
  c_cnt_wrap:        cover property ($past(result)==8'd0 && ena |=> result==8'hFF);
endmodule

bind counter_down counter_down_sva u_counter_down_sva (.*);