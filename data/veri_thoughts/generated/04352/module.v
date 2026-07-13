module phase_accumulator #
(
    parameter WIDTH = 32,
    parameter INITIAL_PHASE = 0,
    parameter INITIAL_PHASE_STEP = 0
)
(
    input  wire             clk,
    input  wire             rst,

    
    input  wire [WIDTH-1:0] input_phase_tdata,
    input  wire             input_phase_tvalid,
    output wire             input_phase_tready,

    
    input  wire [WIDTH-1:0] input_phase_step_tdata,
    input  wire             input_phase_step_tvalid,
    output wire             input_phase_step_tready,

    
    output wire [WIDTH-1:0] output_phase_tdata,
    output wire             output_phase_tvalid,
    input  wire             output_phase_tready
);

reg [WIDTH-1:0] phase_reg = INITIAL_PHASE;
reg [WIDTH-1:0] phase_step_reg = INITIAL_PHASE_STEP;

assign input_phase_tready = output_phase_tready;
assign input_phase_step_tready = 1;
assign output_phase_tdata = phase_reg;
assign output_phase_tvalid = 1;

always @(posedge clk) begin
    if (rst) begin
        phase_reg <= INITIAL_PHASE;
        phase_step_reg <= INITIAL_PHASE_STEP;
    end else begin
        if (input_phase_tready & input_phase_tvalid) begin
            phase_reg <= input_phase_tdata;
        end else if (output_phase_tready) begin
            phase_reg <= phase_reg + phase_step_reg;
        end

        if (input_phase_step_tvalid) begin
            phase_step_reg <= input_phase_step_tdata;
        end
    end
end

endmodule