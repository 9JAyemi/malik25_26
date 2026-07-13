
module priority_encoder (
    input [7:0] in,
    output reg [1:0] pos,
    output reg [3:0] out_sel,
    input clk // Added clock input
);

    always @ (posedge clk) begin
        if (in[7]) begin
            pos <= 3'b111;
            out_sel <= 4'b0001;
        end else if (in[6]) begin
            pos <= 3'b110;
            out_sel <= 4'b0010;
        end else if (in[5]) begin
            pos <= 3'b100;
            out_sel <= 4'b0100;
        end else if (in[4]) begin
            pos <= 3'b011;
            out_sel <= 4'b1000;
        end else if (in[3]) begin
            pos <= 3'b010;
            out_sel <= 4'b0000;
        end else if (in[2]) begin
            pos <= 3'b001;
            out_sel <= 4'b0000;
        end else if (in[1]) begin
            pos <= 3'b000;
            out_sel <= 4'b0000;
        end else begin
            pos <= 2'b00;
            out_sel <= 4'b0000;
        end
    end
endmodule
