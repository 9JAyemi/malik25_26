// SVA for diffeq_f_systemC
module diffeq_f_systemC_sva(
  input logic        clk,
  input logic        reset,
  input logic [31:0] aport,
  input logic [31:0] dxport,
  input logic [31:0] xport,
  input logic [31:0] yport,
  input logic [31:0] uport,
  input logic [31:0] temp
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [31:0] add32(input logic [31:0] a, b);
    add32 = logic [31:0]'(a + b);
  endfunction
  function automatic logic [31:0] sub32(input logic [31:0] a, b);
    sub32 = logic [31:0]'(a - b);
  endfunction
  function automatic logic [31:0] mul32(input logic [31:0] a, b);
    mul32 = logic [31:0]'(a * b);
  endfunction

  // Combinational relation
  a_temp_comb: assert property (temp == mul32(uport, dxport));

  // Reset behavior
  a_reset_to_zero: assert property (reset |=> (xport==32'h0 && yport==32'h0 && uport==32'h0));
  a_reset_hold_zero: assert property ((reset && $past(reset))
                                      |-> (xport==32'h0 && yport==32'h0 && uport==32'h0
                                           && $stable({xport,yport,uport})));

  // Functional update when xport < aport
  a_update: assert property (disable iff (reset)
    ($past(!reset) && $past(xport) < $past(aport)) |=> (
      xport == add32($past(xport), $past(dxport)) &&
      yport == add32($past(yport), $past(temp)) &&
      uport == sub32( sub32($past(uport), mul32($past(temp), mul32(32'd5, $past(xport)))),
                      mul32($past(dxport), mul32(32'd3, $past(yport))) )
    ));

  // Hold when xport >= aport
  a_hold: assert property (disable iff (reset)
    ($past(!reset) && !($past(xport) < $past(aport)))
      |=> (xport == $past(xport) && yport == $past(yport) && uport == $past(uport)));

  // No spurious change
  a_change_implies_update: assert property (disable iff (reset)
    ($past(!reset) && ($changed(xport) || $changed(yport) || $changed(uport)))
      |-> $past(xport) < $past(aport));

  // Known on outputs
  a_no_x_outputs: assert property (disable iff (reset) !$isunknown({xport,yport,uport}));

  // Coverage
  c_reset_release: cover property (reset ##1 !reset);
  c_update:        cover property (disable iff (reset)
                      ($past(xport) < $past(aport) && $past(dxport)!=0 && $past(uport)!=0 && $past(yport)!=0)
                        |=> ($changed(xport) && $changed(yport) && $changed(uport)));
  c_hold:          cover property (disable iff (reset)
                      !($past(xport) < $past(aport)) |=> $stable({xport,yport,uport}));
  c_boundary:      cover property (disable iff (reset)
                      ($past(xport) < $past(aport)) && !(xport < aport));
endmodule

// Bind into DUT
bind diffeq_f_systemC diffeq_f_systemC_sva i_diffeq_f_systemC_sva(
  .clk(clk), .reset(reset),
  .aport(aport), .dxport(dxport),
  .xport(xport), .yport(yport), .uport(uport),
  .temp(temp)
);