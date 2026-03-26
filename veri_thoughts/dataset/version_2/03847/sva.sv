module simple_adder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic cin,
    input logic [7:0] sum,
    input logic cout
);

    wire [8:0] temp_sum;
    assign temp_sum = {1'b0, a} + {1'b0, b} + cin;

    // No carry-out passes through the low 8-bit sum.
    check_no_carry_passthrough: assert property (
        @(posedge clk) !temp_sum[8] |-> (sum == temp_sum[7:0] && cout == 1'b0)
    );

    // Carry-out with temp_sum[7] low saturates sum to 8'h7F.
    check_carry_msb0_saturates_7f: assert property (
        @(posedge clk) (temp_sum[8] && !temp_sum[7]) |-> (sum == 8'h7F && cout == 1'b1)
    );

    // Carry-out with temp_sum[7] high saturates sum to 8'h80.
    check_carry_msb1_saturates_80: assert property (
        @(posedge clk) (temp_sum[8] && temp_sum[7]) |-> (sum == 8'h80 && cout == 1'b1)
    );

    // cout matches the carry-out bit of the addition.
    check_cout_matches_carry: assert property (
        @(posedge clk) cout == temp_sum[8]
    );

    // sum always matches the RTL's selected output value.
    check_sum_matches_selected_result: assert property (
        @(posedge clk) sum == (temp_sum[8] ? (temp_sum[7] ? 8'h80 : 8'h7F) : temp_sum[7:0])
    );

endmodule