
module top_module (
    input   clk,
    input   [15:0] A,
    input   [15:0] B,
    input   [3:0] shift_amt,
    output  wire less_than,
    output  wire equal_to,
    output  wire greater_than,
    output  wire [15:0] shifted_A,
    output  wire [15:0] shifted_B,
    output  wire [15:0] final_output
);

    // Instantiate the magnitude comparator module
    magnitude_comparator mag_comp(
        .A(A),
        .B(B),
        .less_than(less_than),
        .equal_to(equal_to),
        .greater_than(greater_than)
    );
    
    // Instantiate the barrel shifter module for input A
    barrel_shifter bar_shifter_A(
        .data_in(A),
        .shift_amt(shift_amt),
        .data_out(shifted_A)
    );
    
    // Instantiate the barrel shifter module for input B
    barrel_shifter bar_shifter_B(
        .data_in(B),
        .shift_amt(shift_amt),
        .data_out(shifted_B)
    );
    
    // Instantiate the functional module for final output calculation
    final_output_calculator final_calc(
        .less_than(less_than),
        .equal_to(equal_to),
        .greater_than(greater_than),
        .shifted_A(shifted_A),
        .shifted_B(shifted_B),
        .final_output(final_output)
    );
    
endmodule
module magnitude_comparator (
    input   [15:0] A,
    input   [15:0] B,
    output  wire less_than,
    output  wire equal_to,
    output  wire greater_than
);

    wire    less_than_int;
    wire    equal_to_int;
    wire    greater_than_int;

    assign  less_than_int = (A < B);
    assign  equal_to_int = (A == B);
    assign  greater_than_int = (A > B);

    assign  less_than = less_than_int;
    assign  equal_to = equal_to_int;
    assign  greater_than = greater_than_int;
    
endmodule
module barrel_shifter (
    input   [15:0] data_in,
    input   [3:0] shift_amt,
    output  wire [15:0] data_out
);

    assign  data_out = (shift_amt == 4'b0000) ? data_in :
                        (shift_amt == 4'b0001) ? {data_in[14:0], 1'b0} :
                        (shift_amt == 4'b0010) ? {data_in[13:0], 2'b00} :
                        (shift_amt == 4'b0011) ? {data_in[12:0], 3'b000} :
                        (shift_amt == 4'b0100) ? {data_in[11:0], 4'b0000} :
                        (shift_amt == 4'b0101) ? {data_in[10:0], 5'b00000} :
                        (shift_amt == 4'b0110) ? {data_in[9:0], 6'b000000} :
                        (shift_amt == 4'b0111) ? {data_in[8:0], 7'b0000000} :
                        (shift_amt == 4'b1000) ? {data_in[7:0], 8'b00000000} :
                        (shift_amt == 4'b1001) ? {data_in[6:0], 9'b000000000} :
                        (shift_amt == 4'b1010) ? {data_in[5:0], 10'b0000000000} :
                        (shift_amt == 4'b1011) ? {data_in[4:0], 11'b00000000000} :
                        (shift_amt == 4'b1100) ? {data_in[3:0], 12'b000000000000} :
                        (shift_amt == 4'b1101) ? {data_in[2:0], 13'b0000000000000} :
                        (shift_amt == 4'b1110) ? {data_in[1:0], 14'b00000000000000} :
                                                {data_in[0], 15'b000000000000000};
    
endmodule
module final_output_calculator (
    input   wire less_than,
    input   wire equal_to,
    input   wire greater_than,
    input   wire [15:0] shifted_A,
    input   wire [15:0] shifted_B,
    output  wire [15:0] final_output
);

    assign  final_output = (less_than) ? (shifted_A - shifted_B) :
                            (equal_to) ? shifted_A :
                            (greater_than) ? (shifted_A + shifted_B) : 16'b0;
    
endmodule