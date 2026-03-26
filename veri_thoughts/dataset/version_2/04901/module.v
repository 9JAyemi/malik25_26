
module barrel_shift (
    input wire [2:0] in_vec,
    output wire [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

    assign o0 = in_vec[0];
    assign o1 = in_vec[1];
    assign o2 = in_vec[2];

    reg [2:0] outv_reg;

    always @(*) begin
        case(in_vec)
            3'b000: outv_reg = in_vec;
            3'b001: outv_reg = {in_vec[0], in_vec[2], in_vec[1]};
            3'b010: outv_reg = {in_vec[1], in_vec[0], in_vec[2]};
            3'b011: outv_reg = {in_vec[1], in_vec[2], in_vec[0]};
            3'b100: outv_reg = {in_vec[2], in_vec[0], in_vec[1]};
            3'b101: outv_reg = {in_vec[2], in_vec[1], in_vec[0]};
            default: outv_reg = in_vec;
        endcase
    end

    assign outv = outv_reg;

endmodule
module top_module ( 
    input wire [2:0] vec,
    output wire [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

    barrel_shift bs(.in_vec(vec), .outv(outv), .o2(o2), .o1(o1), .o0(o0));

endmodule