module my_module(
    input dataa,
    input clk,
    input aclr,
    input ena,
    input devclrn,
    input devpor,
    output reg dataout
);

parameter output_clock = "none";

reg [1:0] state;

initial begin
    state = 2'b00;
end

always @(posedge clk or negedge aclr) begin
    if (!aclr) begin
        state <= 2'b00;
        dataout <= 1'b0;
    end
    else begin
        case (state)
            2'b00: begin
                if (ena) begin
                    dataout <= dataa;
                    state <= 2'b01;
                end
                else begin
                    dataout <= 1'b0;
                end
            end
            2'b01: begin
                if (output_clock != "none") begin
                    state <= 2'b10;
                end
                else begin
                    state <= 2'b00;
                end
            end
            2'b10: begin
                dataout <= dataa;
                state <= 2'b11;
            end
            2'b11: begin
                dataout <= 1'b0;
                state <= 2'b00;
            end
        endcase
    end
end

endmodule