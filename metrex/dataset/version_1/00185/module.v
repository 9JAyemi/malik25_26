module state_machine(
    input wire reset,
    input wire [8:0] in_state,
    output reg out1,
    output reg out2,
    input wire clk
);

always @ (posedge reset or posedge clk) begin
    if (reset) begin
        out1 <= 0;
        out2 <= 0;
    end else begin
        case(in_state)
            9'd0: begin
                out1 <= 0;
                out2 <= 0;
            end
            9'd1: begin
                out1 <= 1;
                out2 <= 0;
            end
            9'd2: begin
                out1 <= 0;
                out2 <= 1;
            end
            default: begin
                out1 <= 0;
                out2 <= 0;
            end
        endcase
    end
end

endmodule