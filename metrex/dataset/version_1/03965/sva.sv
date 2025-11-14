// SVA checker for processing_unit
module processing_unit_sva #(
  parameter PRV_SIZE        = 16,
  parameter PRV_LOOP        = 1,
  parameter WEIGHT_WIDTH    = 3,
  parameter FRACTION_WIDTH  = 8,
  parameter REG_WIDTH       = $clog2(PRV_SIZE*PRV_LOOP*3) + 8 + 1,
  parameter BIAS            = 0
)(
  input logic                         clk_i,
  input logic                         en_i,
  input logic                         rst_i,
  input logic [WEIGHT_WIDTH-1:0]      weight_i,
  input logic [7:0]                   data_i,
  input logic [9:0]                   proc_unit_o,

  // internal signals of DUT (bound by name)
  input logic [9:0]                   product,
  input logic [REG_WIDTH-1:0]         signed_product,
  input logic [REG_WIDTH-1:0]         sum,
  input logic                         positive_cap,
  input logic                         negative_cap
);

  localparam int SIGN_IDX = WEIGHT_WIDTH-1;

  default clocking cb @(posedge clk_i); endclocking

  // Expected combinational product (mirrors DUT)
  function automatic [9:0] exp_product (input logic [WEIGHT_WIDTH-1:0] w, input logic [7:0] d);
    case (w[2:0])
      3'd0: exp_product = 10'd0;
      3'd1: exp_product = {5'd0, d[7:3]};
      3'd2: exp_product = {4'd0, d[7:2]};
      3'd3: exp_product = {3'd0, d[7:1]};
      3'd4: exp_product = d[7:1] + d[7:2];
      3'd5: exp_product = d;
      3'd6: exp_product = d + d[7:2];
      3'd7: exp_product = d + d[7:1];
    endcase
  endfunction

  function automatic [REG_WIDTH-1:0] zext10(input logic [9:0] x);
    zext10 = {{(REG_WIDTH-10){1'b0}}, x};
  endfunction

  function automatic [REG_WIDTH-1:0] negext10(input logic [9:0] x);
    negext10 = {{(REG_WIDTH-10){1'b1}}, (~x + 10'd1)};
  endfunction

  // Combinational decode checks
  assert property (product == exp_product(weight_i, data_i))
    else $error("product decode mismatch");

  assert property ( (!weight_i[SIGN_IDX] || (product==10'd0)) |-> (signed_product == zext10(product)) )
    else $error("signed_product zero-extend mismatch");

  assert property ( (weight_i[SIGN_IDX] && (product!=10'd0)) |-> (signed_product == negext10(product)) )
    else $error("signed_product neg-extend mismatch");

  // positive_cap / negative_cap definitions
  assert property ( positive_cap == (sum[REG_WIDTH-2:11] != '0) )
    else $error("positive_cap definition mismatch");

  assert property ( negative_cap == !(sum[REG_WIDTH-2:11] == {(REG_WIDTH-12){1'b1}}) )
    else $error("negative_cap definition mismatch");

  // Sum register behavior
  assert property ( rst_i |=> (sum == BIAS) )
    else $error("sum not set to BIAS on reset");

  assert property ( disable iff (rst_i) (!en_i) |-> (sum == $past(sum)) )
    else $error("sum changed while en_i=0");

  assert property ( disable iff (rst_i) (en_i) |-> (sum == $past(sum) + $past(signed_product)) )
    else $error("sum did not accumulate correctly");

  // Output saturation/rounding behavior with priority
  // Priority 1: positive saturation
  assert property ( (positive_cap && !sum[REG_WIDTH-1]) |-> (proc_unit_o == 10'b0111111111) )
    else $error("proc_unit_o positive saturation mismatch");

  // Priority 2: negative saturation (only if pos-sat not taken)
  assert property ( (!(positive_cap && !sum[REG_WIDTH-1]) &&
                     ((negative_cap || (sum[11:2]==10'b1000000000)) && sum[REG_WIDTH-1]))
                    |-> (proc_unit_o == 10'b1000000001) )
    else $error("proc_unit_o negative saturation mismatch");

  // Priority 3: pass-through
  assert property ( (!(positive_cap && !sum[REG_WIDTH-1]) &&
                     !(((negative_cap || (sum[11:2]==10'b1000000000)) && sum[REG_WIDTH-1])))
                    |-> (proc_unit_o == sum[11:2]) )
    else $error("proc_unit_o pass-through mismatch");

  // -------- Coverage --------
  // Reset then BIAS
  cover property ( $rose(rst_i) ##1 (sum == BIAS) );

  // All weight decode cases seen
  genvar wi;
  generate
    for (wi=0; wi<8; wi++) begin : C_WEIGHT
      cover property ( !rst_i && (weight_i[2:0] == wi[2:0]) );
    end
  endgenerate

  // Signed product paths
  cover property ( !rst_i && weight_i[SIGN_IDX] && (product!=10'd0) ); // negative, non-zero
  cover property ( !rst_i && weight_i[SIGN_IDX] && (product==10'd0) ); // negative, zero

  // Accumulate and hold
  cover property ( !rst_i && en_i );
  cover property ( !rst_i && !en_i );

  // Saturation events
  cover property ( !rst_i && positive_cap && !sum[REG_WIDTH-1] ); // +sat
  cover property ( !rst_i && ((negative_cap || (sum[11:2]==10'b1000000000)) && sum[REG_WIDTH-1]) ); // -sat

  // Pass-through (no saturation)
  cover property ( !rst_i &&
                   !(positive_cap && !sum[REG_WIDTH-1]) &&
                   !(((negative_cap || (sum[11:2]==10'b1000000000)) && sum[REG_WIDTH-1])) );

  // Negative boundary special-case
  cover property ( !rst_i && sum[REG_WIDTH-1] && (sum[11:2]==10'b1000000000) );

endmodule

// Bind into the DUT (connects by name, including internals)
bind processing_unit processing_unit_sva #(
  .PRV_SIZE(PRV_SIZE),
  .PRV_LOOP(PRV_LOOP),
  .WEIGHT_WIDTH(WEIGHT_WIDTH),
  .FRACTION_WIDTH(FRACTION_WIDTH),
  .REG_WIDTH(REG_WIDTH),
  .BIAS(BIAS)
) u_processing_unit_sva (.*);