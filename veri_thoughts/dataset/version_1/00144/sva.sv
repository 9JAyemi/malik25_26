// SVA checker for reg_unit
module reg_unit_sva #(parameter ff_sz=8)
(
  input  logic                  clk,
  input  logic                  rst,   // active-low async reset
  input  logic                  load,
  input  logic [ff_sz-1:0]      data_in,
  input  logic [ff_sz-1:0]      data_out
);

  // Async reset must clear immediately at negedge rst (account for NBA with ##0)
  assert property (@(negedge rst) ##0 (data_out == '0))
    else $error("data_out not cleared on async reset");

  // While in reset, output must be 0 at each clk edge
  assert property (@(posedge clk) (!rst) |-> (data_out == '0))
    else $error("data_out not 0 while rst=0");

  // When loading (rst high), update occurs on the same clock edge
  assert property (@(posedge clk) disable iff (!rst) load |-> ##0 (data_out == data_in))
    else $error("Load did not capture data_in on same edge");

  // When not loading and no reset across the boundary, output holds (same-edge check)
  assert property (@(posedge clk) disable iff (!rst || !$past(rst))
                   !load |-> ##0 (data_out == $past(data_out)))
    else $error("data_out changed without load");

  // X checks
  assert property (@(posedge clk) disable iff (!rst) !$isunknown(data_out))
    else $error("data_out has X/Z while out of reset");
  assert property (@(posedge clk) disable iff (!rst) load |-> !$isunknown(data_in))
    else $error("data_in has X/Z when being loaded");

  // Coverage
  cover property (@(negedge rst) ##0 (data_out == '0));                 // async reset observed
  cover property (@(posedge clk) disable iff (!rst) load);              // a load occurs
  cover property (@(posedge clk) disable iff (!rst) load [*2]);         // back-to-back loads
  cover property (@(posedge clk) disable iff (!rst || !$past(rst))
                  !load ##1 !load && $stable(data_out));                // hold over a cycle
endmodule

// Bind into the DUT
bind reg_unit reg_unit_sva #(.ff_sz(ff_sz)) reg_unit_sva_i (
  .clk(clk), .rst(rst), .load(load), .data_in(data_in), .data_out(data_out)
);