
module byte_counter (
    input wire [15:0] in,
    input wire [7:0] in_vec,
    output reg [7:0] out
);

// Split input word into two bytes
wire [7:0] upper_byte = in[15:8];
wire [7:0] lower_byte = in[7:0];

// Count number of 1's in upper byte
wire [7:0] upper_count;
barrel_shifter barrel_upper(.in(upper_byte), .out(upper_count));

// Count number of 1's in lower byte
wire [7:0] lower_count;
barrel_shifter barrel_lower(.in(lower_byte), .out(lower_count));

// Count number of 1's in input vector
wire [7:0] vec_count;
barrel_shifter barrel_vec(.in(in_vec), .out(vec_count));

// Add the three counts
wire [8:0] sum;
binary_tree_adder adder(.in({upper_count, lower_count, vec_count}), .out(sum));

// Output the sum
always @(*)
    out = sum[7:0];

endmodule
module barrel_shifter (
    input wire [7:0] in,
    output reg [7:0] out
);

// Shift input left by 1, 2, 4, 8 bits and add results
wire [7:0] shift1 = {in[6:0], 1'b0};
wire [7:0] shift2 = {in[5:0], 2'b00};
wire [7:0] shift4 = {in[3:0], 4'b0000};
wire [7:0] shift8 = {in[0], 7'b0000000};
wire [7:0] sum1 = shift1 + in;
wire [7:0] sum2 = shift2 + sum1;
wire [7:0] sum4 = shift4 + sum2;
wire [7:0] sum8 = shift8 + sum4;

// Output sum8
always @(*)
    out = sum8;

endmodule
module binary_tree_adder (
    input wire [23:0] in,
    output reg [8:0] out
);

// Add pairs of adjacent bits until only one bit is left
wire [22:0] sum1 = in[0] + in[1];
wire [21:0] sum2 = sum1[0] + sum1[1];
wire [20:0] sum3 = sum2[0] + sum2[1];
wire [19:0] sum4 = sum3[0] + sum3[1];
wire [18:0] sum5 = sum4[0] + sum4[1];
wire [17:0] sum6 = sum5[0] + sum5[1];
wire [16:0] sum7 = sum6[0] + sum6[1];
wire [15:0] sum8 = sum7[0] + sum7[1];
wire [14:0] sum9 = sum8[0] + sum8[1];
wire [13:0] sum10 = sum9[0] + sum9[1];
wire [12:0] sum11 = sum10[0] + sum10[1];
wire [11:0] sum12 = sum11[0] + sum11[1];
wire [10:0] sum13 = sum12[0] + sum12[1];
wire [9:0] sum14 = sum13[0] + sum13[1];
wire [8:0] sum15 = sum14[0] + sum14[1];

// Output sum15
always @(*)
    out = sum15;

endmodule