module top_module_sva (
    input logic a,
    input logic b,
    input logic [2:0] a_bitwise,
    input logic [2:0] b_bitwise,
    output logic [2:0] out_sum
); 

    wire cout;
    wire sum;
    wire [2:0] out_or_bitwise;
    wire out_or_logical;
    wire [5:0] out_not;
    wire [2:0] out_final;
    
    half_adder ha(a, b, cout, sum);
    bitwise_OR bo(a_bitwise, b_bitwise, out_or_bitwise, out_or_logical, out_not);
    functional_module fm(cout, sum, out_or_bitwise, out_or_logical, out_not, out_final);
    
    assign out_sum = out_final;
    
    // Check that the sum is calculated correctly
    sum_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) sum == a ^ b
    );
    
    // Check that the carry out is calculated correctly
    carry_out_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) cout == a & b
    );
    
    // Check that the bitwise OR of a_bitwise and b_bitwise is calculated correctly
    bitwise_or_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) out_or_bitwise == a_bitwise | b_bitwise
    );
    
    // Check that the logical OR of a_bitwise and b_bitwise is calculated correctly
    logical_or_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) out_or_logical == |{a_bitwise, b_bitwise}
    );
    
    // Check that the bitwise NOT of a_bitwise and b_bitwise is calculated correctly
    bitwise_not_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) out_not == ~{a_bitwise, b_bitwise}
    );
    
    // Check that the final output is calculated correctly
    final_output_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) out_final == sum + out_or_bitwise
    );
    
    // Check that the output sum is assigned correctly
    output_assignment: assert property (
        @(posedge clk) disable iff (!reset_n) out_sum == out_final
    );
    
    // Check that the carry out is not asserted when a and b are both 0
    carry_out_zero: assert property (
        @(posedge clk) disable iff (!reset_n) (a == 0 && b == 0) |-> cout == 0
    );
    
    // Check that the sum is not asserted when a and b are both 1
    sum_one: assert property (
        @(posedge clk) disable iff (!reset_n) (a == 1 && b == 1) |-> sum == 0
    );
    
endmodule