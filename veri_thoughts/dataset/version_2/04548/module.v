
module binary_to_gray (
    input [7:0] binary_in,
    input sel_b1,
    input sel_b2,
    output [7:0] gray_out);

    // Priority encoder to find position of first 1 in binary input
    wire [2:0] pos;
    wire [7:0] not_binary_in = ~binary_in;
    assign pos = not_binary_in > binary_in ? {3'b000, not_binary_in[7:3]} :
                                             not_binary_in > binary_in >> 1 ? {3'b001, not_binary_in[6:2]} :
                                                                             {3'b010, not_binary_in[5:1]};

    // 2-to-1 multiplexer to select between binary input and right shift by 1 bit
    wire [7:0] shift_right = {1'b0, binary_in[7:1]};
    assign gray_out = sel_b1 ? binary_in : (sel_b2 ? shift_right : binary_in);
    
endmodule