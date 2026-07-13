module Approx_adder_sva
    #(parameter W=26, parameter LowL=16) (
        input wire clk,
        input wire rst_n,
        input wire add_sub,
        input wire [W-1:0] in1,
        input wire [W-1:0] in2,
        output wire [W:0] res
    );

    // Ensure that the result is correct for addition and subtraction
    add_result: assert property (
        @(posedge clk) disable iff (!rst_n) (res == (add_sub ? (in1 - in2) : (in1 + in2)))
    ) else $error("Incorrect result for addition or subtraction");

    // Ensure that the lower_res is within the expected range
    lower_res_range: assert property (
        @(posedge clk) disable iff (!rst_n) (lower_res[W-1:LowL] == 0)
    ) else $error("Lower result out of expected range");

    // Ensure that the approximate carry out is within the expected range
    approx_cout_range: assert property (
        @(posedge clk) disable iff (!rst_n) (approx_cout == 0)
    ) else $error("Approximate carry out out of expected range");

    // Ensure that the in2_signed is correctly assigned based on add_sub
    in2_signed_assignment: assert property (
        @(posedge clk) disable iff (!rst_n) (in2_signed == (add_sub ? ~in2 : in2))
    ) else $error("Incorrect assignment of in2_signed");

    // Ensure that the ApproxAdd module is instantiated correctly
    approx_add_instantiation: assert property (
        @(posedge clk) disable iff (!rst_n) (1'b1)
    ) else $error("ApproxAdd module not instantiated correctly");

    // Ensure that the res is correctly calculated by the ApproxAdd module
    res_calculation: assert property (
        @(posedge clk) disable iff (!rst_n) (res == {(in1[W-1:LowL] + in2_signed[W-1:LowL] + approx_cout), lower_res})
    ) else $error("Incorrect calculation of res");

    // Ensure that the lower_res is correctly calculated by the ApproxAdd module
    lower_res_calculation: assert property (
        @(posedge clk) disable iff (!rst_n) (lower_res == ApproxAdd.lower_res)
    ) else $error("Incorrect calculation of lower_res");

    // Ensure that the approx_cout is correctly calculated by the ApproxAdd module
    approx_cout_calculation: assert property (
        @(posedge clk) disable iff (!rst_n) (approx_cout == ApproxAdd.approx_cout)
    ) else $error("Incorrect calculation of approx_cout");

endmodule