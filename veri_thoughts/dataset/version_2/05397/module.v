
module bdd_module (
    input [3:0] in_data,
    input [1:0] op_select,
    output reg [3:0] out_data
);

// BDD-based functional module
always @(*) begin
    case (op_select)
        2'b00: out_data = in_data & 4'b1111; // AND operation
        2'b01: out_data = in_data | 4'b0000; // OR operation
        2'b10: out_data = in_data ^ 4'b1010; // XOR operation
        default: out_data = 4'b0000; // default output
    endcase
end

endmodule
module top_module ( 
    input [2:0] select, 
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input [1:0] op_select, // Changed to 1:0
    output [3:0] out 
);

wire [3:0] mux_out;
wire [3:0] bdd_out;

// 6-to-1 multiplexer
assign mux_out = (select <= 5) ? 
    ((select == 0) ? data0 :
    (select == 1) ? data1 :
    (select == 2) ? data2 :
    (select == 3) ? data3 :
    (select == 4) ? data4 :
    (select == 5) ? data5 : 4'b0000) : 4'b0000;

// BDD-based functional module instantiation
bdd_module bdd_inst (
    .in_data(mux_out),
    .op_select(op_select),
    .out_data(bdd_out)
);

// Output selection based on select input
assign out = (select <= 5) ? mux_out : bdd_out;

endmodule