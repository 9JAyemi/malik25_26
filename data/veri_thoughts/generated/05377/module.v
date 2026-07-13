
module mux_converter (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output wire o2,
    output wire o1,
    output wire o0
);

reg [2:0] priority_sel;
reg [3:0] selected_data;

always @(*) begin
    case (sel)
        3'b000: begin
            priority_sel = 3'b000;
            selected_data = data0;
        end
        3'b001: begin
            priority_sel = 3'b001;
            selected_data = data1;
        end
        3'b010: begin
            priority_sel = 3'b010;
            selected_data = data2;
        end
        3'b011: begin
            priority_sel = 3'b011;
            selected_data = data3;
        end
        3'b100: begin
            priority_sel = 3'b100;
            selected_data = data4;
        end
        3'b101: begin
            priority_sel = 3'b101;
            selected_data = data5;
        end
        default: begin
            priority_sel = 3'b000;
            selected_data = data0;
        end
    endcase
end

assign o2 = selected_data[3];
assign o1 = selected_data[2];
assign o0 = selected_data[1];

endmodule
