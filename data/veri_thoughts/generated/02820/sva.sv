module mux4to1_sva (
    input logic clk,                  // sampling clock for SVA (RTL is combinational, no reset)
    input logic [1:0] sel,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] out
);

    // First-one-hot within a 4-bit vector (LSB priority)
    function automatic logic [3:0] first_one_hot4 (input logic [3:0] v);
        if (v[0])       return 4'b0001;
        else if (v[1])  return 4'b0010;
        else if (v[2])  return 4'b0100;
        else if (v[3])  return 4'b1000;
        else            return 4'b0000;
    endfunction

    // Expected outputs per sel, reflecting global 16-bit priority order
    logic [3:0] expected_sel00, expected_sel01, expected_sel10, expected_sel11;
    always_comb begin
        expected_sel00 = first_one_hot4(in0);
        expected_sel01 = (|in0) ? 4'b0000 : first_one_hot4(in1);
        expected_sel10 = ((|in0) || (|in1)) ? 4'b0000 : first_one_hot4(in2);
        expected_sel11 = ((|in0) || (|in1) || (|in2)) ? 4'b0000 : first_one_hot4(in3);
    end

    // Selected input nibble based on sel
    logic [3:0] selected_in;
    always_comb begin
        unique case (sel)
            2'b00: selected_in = in0;
            2'b01: selected_in = in1;
            2'b10: selected_in = in2;
            default: selected_in = in3;
        endcase
    end

    ///// Functional equivalence to RTL /////
    // For sel==00, out equals first-one-hot of in0.
    check_sel00_functional: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == expected_sel00)
    );
    // For sel==01, out equals first-one-hot of in1 gated by no ones in in0.
    check_sel01_functional: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == expected_sel01)
    );
    // For sel==10, out equals first-one-hot of in2 gated by no ones in in0|in1.
    check_sel10_functional: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == expected_sel10)
    );
    // For sel==11, out equals first-one-hot of in3 gated by no ones in in0|in1|in2.
    check_sel11_functional: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == expected_sel11)
    );

    ///// Basic safety/consistency rules /////
    // Out is always a subset of the selected input nibble.
    check_out_subset_of_selected: assert property (
        @(posedge clk) ((out & ~selected_in) == 4'b0000)
    );
    // Out has at most one bit set (one-hot or zero).
    check_out_onehot0: assert property (
        @(posedge clk) $onehot0(out)
    );

    ///// Priority blocking by earlier nibbles /////
    // If sel==01 and any bit in in0 is 1, out must be zero.
    check_block_by_in0_for_sel01: assert property (
        @(posedge clk) (sel == 2'b01 && (|in0)) |-> (out == 4'b0000)
    );
    // If sel==10 and any bit in in0|in1 is 1, out must be zero.
    check_block_by_in0_in1_for_sel10: assert property (
        @(posedge clk) (sel == 2'b10 && ((|in0) || (|in1))) |-> (out == 4'b0000)
    );
    // If sel==11 and any bit in in0|in1|in2 is 1, out must be zero.
    check_block_by_prev_for_sel11: assert property (
        @(posedge clk) (sel == 2'b11 && ((|in0) || (|in1) || (|in2))) |-> (out == 4'b0000)
    );

    ///// All-zeros input behavior /////
    // If all inputs are zero, out must be zero for any sel.
    check_all_zero_inputs: assert property (
        @(posedge clk) (~(|in0) && ~(|in1) && ~(|in2) && ~(|in3))) |-> (out == 4'b0000)
    );

endmodule