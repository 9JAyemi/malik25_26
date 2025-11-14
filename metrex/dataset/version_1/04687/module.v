module mux_priority_encoder_decoder (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out
);

reg [3:0] mux_out [5:0];
reg [2:0] highest_priority;
reg [2:0] selected_input;

always @(*) begin
    case(sel)
        3'b000: begin
            mux_out[0] = data0;
            mux_out[1] = data1;
            mux_out[2] = data2;
            mux_out[3] = data3;
            mux_out[4] = data4;
            mux_out[5] = data5;
        end
        3'b001: begin
            mux_out[0] = data1;
            mux_out[1] = data0;
            mux_out[2] = data2;
            mux_out[3] = data3;
            mux_out[4] = data4;
            mux_out[5] = data5;
        end
        3'b010: begin
            mux_out[0] = data2;
            mux_out[1] = data0;
            mux_out[2] = data1;
            mux_out[3] = data3;
            mux_out[4] = data4;
            mux_out[5] = data5;
        end
        3'b011: begin
            mux_out[0] = data3;
            mux_out[1] = data0;
            mux_out[2] = data1;
            mux_out[3] = data2;
            mux_out[4] = data4;
            mux_out[5] = data5;
        end
        3'b100: begin
            mux_out[0] = data4;
            mux_out[1] = data0;
            mux_out[2] = data1;
            mux_out[3] = data2;
            mux_out[4] = data3;
            mux_out[5] = data5;
        end
        3'b101: begin
            mux_out[0] = data5;
            mux_out[1] = data0;
            mux_out[2] = data1;
            mux_out[3] = data2;
            mux_out[4] = data3;
            mux_out[5] = data4;
        end
        default: begin
            mux_out[0] = 4'b0000;
            mux_out[1] = 4'b0000;
            mux_out[2] = 4'b0000;
            mux_out[3] = 4'b0000;
            mux_out[4] = 4'b0000;
            mux_out[5] = 4'b0000;
        end
    endcase
end

always @(*) begin
    highest_priority = 3'b000;
    if (mux_out[5] > 4'b0000) begin
        highest_priority = 3'b101;
    end else if (mux_out[4] > 4'b0000) begin
        highest_priority = 3'b100;
    end else if (mux_out[3] > 4'b0000) begin
        highest_priority = 3'b011;
    end else if (mux_out[2] > 4'b0000) begin
        highest_priority = 3'b010;
    end else if (mux_out[1] > 4'b0000) begin
        highest_priority = 3'b001;
    end else if (mux_out[0] > 4'b0000) begin
        highest_priority = 3'b000;
    end
end

always @(*) begin
    case(highest_priority)
        3'b000: begin
            selected_input = 3'b000;
        end
        3'b001: begin
            selected_input = 3'b001;
        end
        3'b010: begin
            selected_input = 3'b010;
        end
        3'b011: begin
            selected_input = 3'b011;
        end
        3'b100: begin
            selected_input = 3'b100;
        end
        3'b101: begin
            selected_input = 3'b101;
        end
        default: begin
            selected_input = 3'b000;
        end
    endcase
end

always @(*) begin
    case(selected_input)
        3'b000: begin
            out = mux_out[0];
        end
        3'b001: begin
            out = mux_out[1];
        end
        3'b010: begin
            out = mux_out[2];
        end
        3'b011: begin
            out = mux_out[3];
        end
        3'b100: begin
            out = mux_out[4];
        end
        3'b101: begin
            out = mux_out[5];
        end
        default: begin
            out = 4'b0000;
        end
    endcase
end

endmodule