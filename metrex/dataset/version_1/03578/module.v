module binary_gray_comparator(
    input [3:0] binary_in, // 4-bit binary input for binary-to-Gray code converter module
    input [3:0] comp_in_1, // 4-bit input 1 for comparator module
    input [3:0] comp_in_2, // 4-bit input 2 for comparator module
    output [3:0] gray_out, // 4-bit Gray code output from binary-to-Gray code converter module
    output comp_out, // 1-bit output from comparator module
    output [3:0] shift_out // 4-bit output from functional module
);

assign gray_out[0] = binary_in[0];
assign gray_out[1] = binary_in[0] ^ binary_in[1];
assign gray_out[2] = binary_in[1] ^ binary_in[2];
assign gray_out[3] = binary_in[2] ^ binary_in[3];

assign comp_out = (comp_in_1[3] == comp_in_2[3]) ? 
                    ((comp_in_1[2] == comp_in_2[2]) ? 
                        ((comp_in_1[1] == comp_in_2[1]) ? 
                            (comp_in_1[0] >= comp_in_2[0]) : 
                        (comp_in_1[1] > comp_in_2[1])) : 
                    (comp_in_1[2] > comp_in_2[2])) : 
                (comp_in_1[3] > comp_in_2[3]);

assign shift_out = (comp_out == 1) ? (gray_out << 1) : (gray_out >> 1);

endmodule