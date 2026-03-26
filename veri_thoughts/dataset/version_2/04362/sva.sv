module parity_generator_checker_sva #(
    parameter string parity_type = "even"
)(
    input logic clk,
    input logic [7:0] data_in,
    input logic parity_in,
    input logic parity_out,
    input logic correct
);

    localparam bit EVEN_MODE = (parity_type == "even");

    generate
        if (EVEN_MODE) begin : gen_even_asserts
            // Even mode outputs the reduction XOR of data_in.
            check_even_parity_out: assert property (
                @(posedge clk) parity_out == (^data_in)
            );

            // Even mode makes data_in and parity_out have even total parity.
            check_even_generated_total_parity: assert property (
                @(posedge clk) (^({data_in, parity_out})) == 1'b0
            );

            // Even mode accepts only even total received parity.
            check_even_correct_flag: assert property (
                @(posedge clk) correct == ~(^({data_in, parity_in}))
            );
        end else begin : gen_odd_asserts
            // Odd mode outputs the inverse of the data reduction XOR.
            check_odd_parity_out: assert property (
                @(posedge clk) parity_out == ~(^data_in)
            );

            // Odd mode makes data_in and parity_out have odd total parity.
            check_odd_generated_total_parity: assert property (
                @(posedge clk) (^({data_in, parity_out})) == 1'b1
            );

            // Odd mode accepts only odd total received parity.
            check_odd_correct_flag: assert property (
                @(posedge clk) correct == (^({data_in, parity_in}))
            );
        end
    endgenerate

    // Matching received and generated parity must be accepted.
    check_accept_matching_parity: assert property (
        @(posedge clk) (parity_in == parity_out) |-> correct
    );

    // Mismatched received and generated parity must be rejected.
    check_reject_mismatched_parity: assert property (
        @(posedge clk) (parity_in != parity_out) |-> !correct
    );

endmodule