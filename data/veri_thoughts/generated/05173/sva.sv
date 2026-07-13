module checksum_sva #(parameter int n = 4) (
    input logic clk,
    input logic [n-1:0] data_in,
    input logic [7:0] checksum_out,
    input logic valid_out
);

    function automatic [7:0] calc_sum(input logic [n-1:0] v);
        integer j;
        begin
            calc_sum = 8'h00;
            for (j = 0; j < n; j = j + 1) begin
                calc_sum = calc_sum + v[j];
            end
        end
    endfunction

    function automatic logic calc_valid(input logic [n-1:0] v);
        reg [7:0] local_sum;
        reg [7:0] local_check;
        begin
            local_sum   = calc_sum(v);
            local_check = local_sum + local_sum;
            calc_valid  = (local_check == 8'hFF);
        end
    endfunction

    // checksum_out matches the accumulated sum of data_in bits.
    check_checksum_matches_sum: assert property (
        @(posedge clk) checksum_out == calc_sum(data_in)
    );

    // valid_out matches the implemented comparison on the computed check value.
    check_valid_matches_check_comparison: assert property (
        @(posedge clk) valid_out == calc_valid(data_in)
    );

    // valid_out never goes high for any input pattern.
    check_valid_never_high: assert property (
        @(posedge clk) valid_out == 1'b0
    );

    // All-zero input produces a zero checksum and deasserted valid_out.
    check_zero_input_outputs_zero: assert property (
        @(posedge clk) (data_in == {n{1'b0}}) |-> (checksum_out == 8'h00 && valid_out == 1'b0)
    );

    // Any one-hot input produces a checksum of one and deasserted valid_out.
    check_onehot_input_outputs_one: assert property (
        @(posedge clk) $onehot(data_in) |-> (checksum_out == 8'h01 && valid_out == 1'b0)
    );

endmodule