// SVA for multiplier_16bit
module multiplier_16bit_sva (
    input logic         clk,
    input logic         reset,
    input logic [15:0]  data_in1,
    input logic [15:0]  data_in2,
    input logic         enable_pipeline,
    input logic [31:0]  product_out,
    input logic [15:0]  partial_product1,
    input logic [15:0]  partial_product2,
    input logic [31:0]  partial_product3,
    input logic [31:0]  partial_product4,
    input logic [31:0]  accumulator
);

default clocking @(posedge clk); endclocking

// Reset clears all regs on the next cycle
assert property ($past(reset,1,1'b0) |-> (partial_product1==0 && partial_product2==0 &&
                                          partial_product3==0 && partial_product4==0 &&
                                          accumulator==0 && product_out==0));

// Pipeline disabled: internal pipeline regs hold their values
assert property ($past(!reset && !enable_pipeline,1,1'b0) |->
                 (partial_product1==$past(partial_product1) &&
                  partial_product2==$past(partial_product2) &&
                  partial_product3==$past(partial_product3) &&
                  partial_product4==$past(partial_product4) &&
                  accumulator==$past(accumulator)));

// Bypass result correctness (checked one cycle late)
assert property ($past(!reset && !enable_pipeline,1,1'b0) |->
                 $past(product_out) == ($past(data_in1) * $past(data_in2)));

// Pipeline stage 1 captures inputs
assert property ($past(!reset && enable_pipeline,1,1'b0) |->
                 (partial_product1==$past(data_in1) && partial_product2==$past(data_in2)));

// Pipeline stage 2: multiply previous stage 1 regs
assert property ($past(!reset && enable_pipeline,1,1'b0) |->
                 partial_product3 == ($past(partial_product1) * $past(partial_product2)));

// Pipeline stage 3: add lower 16 bits of product to product
assert property ($past(!reset && enable_pipeline,1,1'b0) |->
                 partial_product4 == ($past(partial_product3) + {16'b0, $past(partial_product3)[15:0]}));

// Pipeline stage 4: accumulate
assert property ($past(!reset && enable_pipeline,1,1'b0) |->
                 accumulator == ($past(accumulator) + $past(partial_product4)));

// Pipeline stage 5: output previous accumulator
assert property ($past(!reset && enable_pipeline,1,1'b0) |->
                 product_out == $past(accumulator));

// No X/Z on outputs and key state after reset deasserts
assert property ($past(reset,1,1'b0) && !reset |-> !$isunknown({product_out, accumulator,
                                                                partial_product4, partial_product3,
                                                                partial_product2, partial_product1}));

// Coverage
cover property (reset ##1 !reset);                              // reset deasserts
cover property (!reset and !enable_pipeline ##1 !enable_pipeline); // stay in bypass
cover property (!reset and enable_pipeline [*5]);               // 5-cycle pipeline burst
cover property (!reset and enable_pipeline ##1 !enable_pipeline ##1 enable_pipeline); // toggle modes

endmodule

bind multiplier_16bit multiplier_16bit_sva sva_i (
    .clk(clk),
    .reset(reset),
    .data_in1(data_in1),
    .data_in2(data_in2),
    .enable_pipeline(enable_pipeline),
    .product_out(product_out),
    .partial_product1(partial_product1),
    .partial_product2(partial_product2),
    .partial_product3(partial_product3),
    .partial_product4(partial_product4),
    .accumulator(accumulator)
);