module d_ff_en_parameterized #(parameter WIDTH = 32) (
    input [WIDTH-1:0] D,
    input CLK,
    input FSM_sequential_state_reg_reg_1,
    input FSM_sequential_state_reg_reg_2,
    output [WIDTH-1:0] Q
);

reg [WIDTH-1:0] Q_reg;

always @(posedge CLK) begin
    if (FSM_sequential_state_reg_reg_1) begin
        Q_reg <= 0;
    end else if (FSM_sequential_state_reg_reg_2) begin
        Q_reg <= D;
    end
end

assign Q = Q_reg;

endmodule