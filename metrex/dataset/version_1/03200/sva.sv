// SVA checker for both synchronizer modules
module sync_sva #(parameter int n = 3)
(
  input  logic        data_in,
  input  logic        clk_in,
  input  logic        rst,        // active-low reset in DUT; here 1=not in reset
  input  logic        data_out,
  input  logic        clk_out,
  input  logic [n-1:0] sync_data, // internal regs (bound)
  input  logic [n-1:0] sync_clk
);

  // Elaboration-time parameter sanity
  initial begin
    assert (n >= 2) else $error("%m: parameter n must be >= 2 for shift slice validity");
  end

  default clocking cb @(posedge clk_in); endclocking
  default disable iff (!rst); // disable checks while in reset

  // Asynchronous reset must clear flops and outputs
  assert property (@(negedge rst) 1'b1 |=> (sync_data == '0 && sync_clk == '0 && data_out == 1'b0 && clk_out == 1'b0))
    else $error("%m: async reset did not clear state/outputs");

  // While held in reset, state/outputs remain 0
  assert property (@(posedge clk_in) !rst |-> (sync_data == '0 && sync_clk == '0 && data_out == 1'b0 && clk_out == 1'b0))
    else $error("%m: values not held at 0 during reset");

  // Output connectivity to last stage
  assert property (data_out == sync_data[n-1]) else $error("%m: data_out not tied to MSB stage");
  assert property (clk_out  == sync_clk [n-1]) else $error("%m: clk_out not tied to MSB stage");

  // Single-cycle shift behavior (vector form)
  assert property (sync_data == { $past(sync_data[n-2:0]), $past(data_in) })
    else $error("%m: data shift chain incorrect");
  assert property (sync_clk  == { $past(sync_clk [n-2:0]), $past(clk_in)  })
    else $error("%m: clk shift chain incorrect");

  // End-to-end n-cycle delay once pipeline is filled (after n cycles out of reset)
  sequence filled_n; rst ##1 rst[* (n-1)]; endsequence
  assert property (filled_n |=> data_out == $past(data_in, n))
    else $error("%m: data_out != data_in delayed by n cycles after fill");
  assert property (filled_n |=> clk_out  == $past(clk_in , n))
    else $error("%m: clk_out != clk_in  delayed by n cycles after fill");

  // No X/Z on outputs when not in reset
  assert property (!$isunknown({data_out, clk_out}))
    else $error("%m: X/Z detected on outputs when not in reset");

  // Coverage: edges propagate through n-stage pipeline
  cover property (filled_n |=> $rose(data_in) ##[n] $rose(data_out));
  cover property (filled_n |=> $fell(data_in) ##[n] $fell(data_out));
  // Coverage: clk_out reaches 1 after fill (as implied by shifting clk_in=1 at posedges)
  cover property (@(posedge clk_in) rst ##1 rst[* (n-1)] ##1 (clk_out == 1'b1));

endmodule

// Bind SVA to both DUTs (including internal shift registers)
bind synchronizer         sync_sva #(.n(n)) i_sync_sva (.* , .sync_data(sync_data), .sync_clk(sync_clk));
bind synchronizer_reverse sync_sva #(.n(n)) i_sync_sva (.* , .sync_data(sync_data), .sync_clk(sync_clk));