module MIPS_Shifter_sva (
    input logic clk,                 // Assertion sampling clock (RTL has no clock/reset)
    input logic [31:0] Data_in,
    input logic [4:0]  Count,
    input logic [1:0]  Sel,
    input logic [31:0] Data_out
);
    // No shift when Count is zero, regardless of Sel.
    check_no_shift_when_count_zero: assert property (
        @(posedge clk) (Count == 5'd0) |-> (Data_out == Data_in)
    );

    // Sel=00: left logical shift by Count.
    check_sll_behavior: assert property (
        @(posedge clk) (Sel == 2'b00) |-> (Data_out == (Data_in << Count))
    );

    // Sel=01: right logical shift by Count.
    check_srl_behavior: assert property (
        @(posedge clk) (Sel == 2'b01) |-> (Data_out == (Data_in >> Count))
    );

    // Sel=10: right arithmetic shift by Count (sign-extend).
    check_sra_behavior: assert property (
        @(posedge clk) (Sel == 2'b10) |-> (Data_out == ($signed(Data_in) >>> Count))
    );

    // Sel=11: rotate-right by Count (exclude Count==0, covered above).
    check_ror_behavior: assert property (
        @(posedge clk) ((Sel == 2'b11) && (Count != 5'd0)) |-> (Data_out == ((Data_in >> Count) | (Data_in << (32 - Count))))
    );

    // For SRA with MSB=0, result equals logical right shift.
    check_sra_equals_srl_when_msb0: assert property (
        @(posedge clk) ((Sel == 2'b10) && (Data_in[31] == 1'b0)) |-> (Data_out == (Data_in >> Count))
    );

    // For SRA with MSB=1 and nonzero shift, MSB of result remains 1.
    check_sra_msb_one_when_shifted: assert property (
        @(posedge clk) ((Sel == 2'b10) && (Data_in[31] == 1'b1) && (Count != 5'd0)) |-> (Data_out[31] == 1'b1)
    );

    // SLL by 1 when Count==1.
    check_sll_by_1: assert property (
        @(posedge clk) ((Sel == 2'b00) && (Count == 5'd1)) |-> (Data_out == {Data_in[30:0], 1'b0})
    );

    // SRL by 2 when Count==2.
    check_srl_by_2: assert property (
        @(posedge clk) ((Sel == 2'b01) && (Count == 5'd2)) |-> (Data_out == {2'b00, Data_in[31:2]})
    );

    // SRA by 4 when Count==4.
    check_sra_by_4: assert property (
        @(posedge clk) ((Sel == 2'b10) && (Count == 5'd4)) |-> (Data_out == {{4{Data_in[31]}}, Data_in[31:4]})
    );

    // ROR by 8 when Count==8.
    check_ror_by_8: assert property (
        @(posedge clk) ((Sel == 2'b11) && (Count == 5'd8)) |-> (Data_out == {Data_in[7:0], Data_in[31:8]})
    );
endmodule