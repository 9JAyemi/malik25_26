module top_module_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic [31:0] in,
    input logic [31:0] out
);
    // Out equals zero-extended 16b add/sub OR'd with byte-reversed 'in'.
    check_functional_equivalence: assert property (
        @(posedge CLK) out == ({16'b0, (sub ? (a[15:0] - b[15:0]) : (a[15:0] + b[15:0]))} |
                               {in[7:0], in[15:8], in[23:16], in[31:24]})
    );

    // Upper 16 bits of out are the upper two reversed bytes of 'in'.
    check_upper16_from_in: assert property (
        @(posedge CLK) out[31:16] == {in[7:0], in[15:8]}
    );

    // Lower 16 bits of out are OR of adder result and reversed low two bytes of 'in'.
    check_lower16_or_composition: assert property (
        @(posedge CLK) out[15:0] == ((sub ? (a[15:0] - b[15:0]) : (a[15:0] + b[15:0])) |
                                     {in[23:16], in[31:24]})
    );

    // When sub=0, out matches sum path merged with byte reversal.
    check_sum_path: assert property (
        @(posedge CLK) !sub |-> out == ({16'b0, (a[15:0] + b[15:0])} |
                                        {in[7:0], in[15:8], in[23:16], in[31:24]})
    );

    // When sub=1, out matches subtract path merged with byte reversal.
    check_sub_path: assert property (
        @(posedge CLK) sub |-> out == ({16'b0, (a[15:0] - b[15:0])} |
                                       {in[7:0], in[15:8], in[23:16], in[31:24]})
    );

    // If low two bytes of 'in' are zero, lower 16 bits equal pure adder result.
    check_lower16_equals_adder_when_in_low_zero: assert property (
        @(posedge CLK) ((in[31:24] == 8'h00) && (in[23:16] == 8'h00)) |-> 
            (out[15:0] == (sub ? (a[15:0] - b[15:0]) : (a[15:0] + b[15:0])))
    );

    // If low two bytes of 'in' are 0xFF, lower 16 bits are all ones.
    check_lower16_all_ones_when_in_low_ff: assert property (
        @(posedge CLK) ((in[31:24] == 8'hFF) && (in[23:16] == 8'hFF)) |-> 
            (out[15:0] == 16'hFFFF)
    );

    // If adder result is zero, lower 16 bits mirror reversed low two bytes of 'in'.
    check_lower16_equals_rev_when_adder_zero: assert property (
        @(posedge CLK) ((sub ? (a[15:0] - b[15:0]) : (a[15:0] + b[15:0])) == 16'h0000) |-> 
            (out[15:0] == {in[23:16], in[31:24]})
    );

    // If upper two bytes of 'in' are zero, upper 16 bits of out are zero.
    check_upper16_zero_when_in_upper_zero: assert property (
        @(posedge CLK) ((in[7:0] == 8'h00) && (in[15:8] == 8'h00)) |-> 
            (out[31:16] == 16'h0000)
    );

    // If adder result is zero, out equals the byte-reversed 'in'.
    check_full_equals_byterev_when_adder_zero: assert property (
        @(posedge CLK) ((sub ? (a[15:0] - b[15:0]) : (a[15:0] + b[15:0])) == 16'h0000) |-> 
            (out == {in[7:0], in[15:8], in[23:16], in[31:24]})
    );
endmodule