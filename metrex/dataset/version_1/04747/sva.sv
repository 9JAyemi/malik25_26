// SVA checker for mkRouterOutputArbitersStatic
// Concise, full functional checks + focused coverage

module router_output_arbs_static_sva
(
  input  logic        CLK,
  input  logic        RST_N,

  input  logic [4:0]  output_arbs_0_select_requests,
  input  logic [4:0]  output_arbs_0_select,

  input  logic [4:0]  output_arbs_1_select_requests,
  input  logic [4:0]  output_arbs_1_select,

  input  logic [4:0]  output_arbs_2_select_requests,
  input  logic [4:0]  output_arbs_2_select,

  input  logic [4:0]  output_arbs_3_select_requests,
  input  logic [4:0]  output_arbs_3_select,

  input  logic [4:0]  output_arbs_4_select_requests,
  input  logic [4:0]  output_arbs_4_select
);

  // Generic checker for a 5-way static-rotating priority encoder
  module arb_checker #(int START = 0)
  (
    input logic       clk,
    input logic       rst_n,
    input logic [4:0] req,
    input logic [4:0] sel
  );
    function automatic logic [4:0] pri_enc(input logic [4:0] r, input int start);
      logic [4:0] res;
      res = '0;
      for (int t = 0; t < 5; t++) begin
        int idx = (start + 5 - t) % 5; // order: START, START-1, ..., wrap
        if (r[idx]) begin
          res[idx] = 1'b1;
          break;
        end
      end
      return res;
    endfunction

    // No X/Z after reset deassertion
    assert property (@(posedge clk) disable iff (!rst_n)
                     !$isunknown({req, sel}));

    // Exact functional equivalence to rotated priority encode
    assert property (@(posedge clk) disable iff (!rst_n)
                     sel == pri_enc(req, START));

    // Basic invariants (redundant with equivalence but useful and cheap)
    assert property (@(posedge clk) disable iff (!rst_n) $onehot0(sel));
    assert property (@(posedge clk) disable iff (!rst_n) (sel & ~req) == '0);
    assert property (@(posedge clk) disable iff (!rst_n)
                     (req != '0) |-> $onehot(sel));
    assert property (@(posedge clk) disable iff (!rst_n)
                     (req == '0) |-> (sel == '0));

    // Output stability when inputs to this arbiter are stable
    assert property (@(posedge clk) disable iff (!rst_n)
                     $stable(req) |-> $stable(sel));

    // Focused coverage
    // - Each singleton request grants itself
    for (genvar k = 0; k < 5; k++) begin : C_SINGLE
      localparam logic [4:0] ONE_HOT = (5'b00001 << k);
      cover property (@(posedge clk) disable iff (!rst_n)
                      (req == ONE_HOT) && sel[k]);
    end
    // - All requests high grants according to START
    cover property (@(posedge clk) disable iff (!rst_n)
                    (req == 5'b11111) && sel[START]);
    // - No requests -> no grant
    cover property (@(posedge clk) disable iff (!rst_n)
                    (req == 5'b00000) && (sel == 5'b00000));
  endmodule

  // Instantiate checkers for each arbiter with its START index
  // Priority orders:
  //   arb0: 4,3,2,1,0   (START=4)
  //   arb1: 0,4,3,2,1   (START=0)
  //   arb2: 1,0,4,3,2   (START=1)
  //   arb3: 2,1,0,4,3   (START=2)
  //   arb4: 3,2,1,0,4   (START=3)
  arb_checker #(.START(4)) chk0 (.clk(CLK), .rst_n(RST_N),
                                 .req(output_arbs_0_select_requests),
                                 .sel(output_arbs_0_select));

  arb_checker #(.START(0)) chk1 (.clk(CLK), .rst_n(RST_N),
                                 .req(output_arbs_1_select_requests),
                                 .sel(output_arbs_1_select));

  arb_checker #(.START(1)) chk2 (.clk(CLK), .rst_n(RST_N),
                                 .req(output_arbs_2_select_requests),
                                 .sel(output_arbs_2_select));

  arb_checker #(.START(2)) chk3 (.clk(CLK), .rst_n(RST_N),
                                 .req(output_arbs_3_select_requests),
                                 .sel(output_arbs_3_select));

  arb_checker #(.START(3)) chk4 (.clk(CLK), .rst_n(RST_N),
                                 .req(output_arbs_4_select_requests),
                                 .sel(output_arbs_4_select));

endmodule

// Bind into the DUT
bind mkRouterOutputArbitersStatic router_output_arbs_static_sva u_router_output_arbs_static_sva (
  .CLK(CLK),
  .RST_N(RST_N),

  .output_arbs_0_select_requests(output_arbs_0_select_requests),
  .output_arbs_0_select         (output_arbs_0_select),

  .output_arbs_1_select_requests(output_arbs_1_select_requests),
  .output_arbs_1_select         (output_arbs_1_select),

  .output_arbs_2_select_requests(output_arbs_2_select_requests),
  .output_arbs_2_select         (output_arbs_2_select),

  .output_arbs_3_select_requests(output_arbs_3_select_requests),
  .output_arbs_3_select         (output_arbs_3_select),

  .output_arbs_4_select_requests(output_arbs_4_select_requests),
  .output_arbs_4_select         (output_arbs_4_select)
);