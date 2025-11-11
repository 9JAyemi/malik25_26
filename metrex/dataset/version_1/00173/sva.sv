// SVA for top_module. Bind this to the DUT.
// Focused, concise checks plus essential coverage.

module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [15:0]  in,
  input logic         select,
  input logic [7:0]   out_hi,
  input logic [7:0]   out_lo,
  input logic [1023:0] out_demux
);

  default clocking cb @(posedge clk); endclocking

  // Expected 256-bit one-hot (only bits [15:0] can ever be 1 due to 4-bit select)
  function automatic logic [255:0] demux_exp(input logic [3:0] s);
    demux_exp = 256'b1 << s;
  endfunction

  // Basic X-checks on outputs (helps catch drive issues)
  assert property (disable iff (reset) !$isunknown(out_hi));
  assert property (disable iff (reset) !$isunknown(out_lo));
  assert property (disable iff (reset) !$isunknown(out_demux));

  // Demux/output bus behavior
  // Upper 768 bits must always be 0 (RHS width truncation/extension in DUT)
  assert property (disable iff (reset) out_demux[1023:256] == '0)
    else $error("out_demux[1023:256] not zero");

  // When select=1, demux output is fully gated off
  assert property (disable iff (reset) select |-> (out_demux == '0))
    else $error("out_demux not zero when select=1");

  // When select=0, lower 256 bits match one-hot decode of in[3:0]
  assert property (disable iff (reset) !select |-> (out_demux[255:0] == demux_exp(in[3:0]) &&
                                                    out_demux[1023:256] == '0))
    else $error("out_demux decode mismatch when select=0");

  // Stronger one-hot sanity on the only reachable range
  assert property (disable iff (reset) !select |-> $onehot(out_demux[15:0]))
    else $error("out_demux[15:0] not onehot when select=0");
  assert property (disable iff (reset) !select |-> (out_demux[255:16] == '0))
    else $error("out_demux[255:16] not zero when select=0");

  // Mux/output behavior
  // out_hi is gated off when select=0
  assert property (disable iff (reset) !select |-> (out_hi == 8'h00))
    else $error("out_hi not zero when select=0");

  // When select=1, out_hi reflects mux selection:
  // sel==0 -> in[7:0], sel!=0 -> in[15:8]
  assert property (disable iff (reset)
                   select |-> (out_hi == ((in[11:10]==2'b00) ? in[7:0] : in[15:8])))
    else $error("out_hi mux mismatch when select=1");

  // out_lo is functionally tied to 0 in the given RTL
  assert property (disable iff (reset) out_lo == 8'h00)
    else $error("out_lo is not zero");

  // Minimal, targeted coverage
  // Cover both select phases
  cover property (disable iff (reset) !select ##1 select);
  cover property (disable iff (reset) select ##1 !select);

  // Cover both mux data paths when enabled
  cover property (disable iff (reset) select && (in[11:10]==2'b00) && (out_hi == in[7:0]));
  cover property (disable iff (reset) select && (in[11:10]!=2'b00) && (out_hi == in[15:8]));

  // Cover all 16 reachable demux addresses when select=0
  genvar v;
  generate
    for (v=0; v<16; v++) begin : C_DEMUX_16
      cover property (disable iff (reset)
                      (!select && in[3:0]==v && out_demux[15:0]==(16'b1<<v)));
    end
  endgenerate

endmodule

// Bind into the DUT
bind top_module top_module_sva top_module_sva_i (.*);