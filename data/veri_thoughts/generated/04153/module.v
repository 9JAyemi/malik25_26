
module multiplexer_4to1(
    input [3:0] a,
    input sel_b1,
    input sel_b2,
    output reg [3:0] out_always
);

// Declare internal wires
wire [3:0] out_reg, out_counter;
wire [1:0] select;

// Instantiate sub-modules
register reg_inst(.in(a), .out(out_reg));
counter counter_inst(.in(a), .out(out_counter));
control_logic control_inst(.sel_b1(sel_b1), .sel_b2(sel_b2), .select(select));

// Always block for output assignment
always @(*) begin
    case (select)
        2'b00: out_always = out_reg;
        2'b01: out_always = out_counter;
        2'b10: out_always = 4'b0000;  // 0000 for 'other' case
        2'b11: out_always = 4'b1111;  // 1111 for 'other' case
    endcase
end

endmodule

module register(
    input [3:0] in,
    output [3:0] out
);

    assign out = in;

endmodule

module counter(
    input [3:0] in,
    output [3:0] out
);

    assign out = in + 1;

endmodule

module control_logic(
    input sel_b1,
    input sel_b2,
    output [1:0] select
);

    assign select = {sel_b2, sel_b1};

endmodule
