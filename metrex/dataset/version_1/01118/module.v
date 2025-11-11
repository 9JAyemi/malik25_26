
module key_Processor(
    input select,
    input [63:0] key,
    output [28:1] lefto,
    output [28:1] righto
);

reg [63:0] temp;

always @ (select or key) begin
    // Perform permutation if select is 1, else pass input key as is
    temp = (select == 1) ? { key[58:57], key[50:49], key[42:41], key[34:33], key[26:25], key[18:17], key[10:9], key[2:1] } : key;
end

// Split the key into left and right halves
assign lefto = temp[63:36];
assign righto = temp[35:2];

endmodule
