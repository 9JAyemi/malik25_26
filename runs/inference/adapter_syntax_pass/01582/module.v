module register_4bit (
    input [3:0] data_in,
    input load,
    input reset,
    input clk,
    output reg [3:0] Q
);

    // Local signals
    reg [3:0] Q_reg;

    // Instantiate 4 D Flip-Flops with Set and Reset functionality
    always @ (posedge clk or posedge reset)
    begin
        if (reset)
        begin
            Q_reg <= 4'b0;
        end
        else if (load)
        begin
            Q_reg <= data_in;
        end
    end

    always @*
    begin
        Q = Q_reg;
    end

endmodule