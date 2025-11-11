// SVA for transition_detector
module td_sva (
  input  logic        clk,
  input  logic        reset,     // active-low async
  input  logic [31:0] in,
  input  logic [31:0] out,

  // internal
  input  logic [31:0] in_reg1, in_reg2, in_reg3, in_reg4,
  input  logic [31:0] out_reg1, out_reg2, out_reg3, out_reg4
);

  localparam logic [31:0] FE = 32'hFFFF_FFFE;
  localparam logic [31:0] FF = 32'hFFFF_FFFF;

  default clocking @(posedge clk); endclocking

  // Async reset clears immediately
  ap_async_clear: assert property (@(negedge reset)
    (in_reg1==0 && in_reg2==0 && in_reg3==0 && in_reg4==0 &&
     out_reg1==0 && out_reg2==0 && out_reg3==0 && out_reg4==0));

  // Output port matches internal register
  ap_out_port: assert property (out == out_reg1);

  // No X/Z on key flops/port when out of reset
  ap_no_x: assert property (disable iff (!reset)
    !$isunknown({out, out_reg1, out_reg2, out_reg3, out_reg4,
                 in_reg1, in_reg2, in_reg3, in_reg4}));

  // Input pipeline integrity (use past values to avoid sampling ambiguity)
  ap_in_pipe: assert property (disable iff (!reset)
    (in_reg2 == $past(in_reg1)) && (in_reg3 == $past(in_reg2)) && (in_reg4 == $past(in_reg3)));

  // Decision based on input delayed by 4 cycles
  function automatic bit past_ok4();
    return reset && $past(reset) && $past(reset,2) && $past(reset,3) && $past(reset,4);
  endfunction

  // FF -> clear all out regs
  ap_ff_clears: assert property (disable iff (!reset)
    (past_ok4() && $past(in,4)==FF)
    |-> (out_reg1==32'd0 && out_reg2==32'd0 && out_reg3==32'd0 && out_reg4==32'd0));

  // FE -> set all out regs to 1
  ap_fe_sets: assert property (disable iff (!reset)
    (past_ok4() && $past(in,4)==FE)
    |-> (out_reg1==32'd1 && out_reg2==32'd1 && out_reg3==32'd1 && out_reg4==32'd1));

  // Default shift when neither FE nor FF
  ap_default_shift: assert property (disable iff (!reset)
    (past_ok4() && !($past(in,4) inside {FE,FF}))
    |-> (out_reg1 == $past(out_reg2) &&
         out_reg2 == $past(out_reg3) &&
         out_reg3 == $past(out_reg4) &&
         out_reg4 == 32'd0));

  // Out regs domain: only 0 or 1 ever appear
  ap_out_domain: assert property (disable iff (!reset)
    (out_reg1 inside {32'd0,32'd1}) &&
    (out_reg2 inside {32'd0,32'd1}) &&
    (out_reg3 inside {32'd0,32'd1}) &&
    (out_reg4 inside {32'd0,32'd1}));

  // Coverage
  cp_seen_FE: cover property (disable iff (!reset) past_ok4() && $past(in,4)==FE);
  cp_seen_FF: cover property (disable iff (!reset) past_ok4() && $past(in,4)==FF);

  // Observe a 4-cycle out==1 pulse followed by 0 (no intervening FE/FF implied)
  cp_pulse4: cover property (disable iff (!reset)
    (out==32'd1) ##1 (out==32'd1) ##1 (out==32'd1) ##1 (out==32'd1) ##1 (out==32'd0));

endmodule

// Bind to DUT
bind transition_detector td_sva td_sva_i (
  .clk     (clk),
  .reset   (reset),
  .in      (in),
  .out     (out),

  .in_reg1 (in_reg1),
  .in_reg2 (in_reg2),
  .in_reg3 (in_reg3),
  .in_reg4 (in_reg4),

  .out_reg1(out_reg1),
  .out_reg2(out_reg2),
  .out_reg3(out_reg3),
  .out_reg4(out_reg4)
);