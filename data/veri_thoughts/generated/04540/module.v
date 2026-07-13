module reset_synchronizer #(
    parameter NUM_RESET_OUTPUT = 1,
    parameter RESET_SYNC_STAGES = 4
) (
    input reset_n,
    input clk,
    output [NUM_RESET_OUTPUT-1:0] reset_n_sync
);


reg [RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:0] reset_reg ;

generate
genvar i;
    for (i=0; i<RESET_SYNC_STAGES+NUM_RESET_OUTPUT-1; i=i+1) begin: reset_stage
        always @(posedge clk or negedge reset_n) begin
            if (~reset_n) begin
                reset_reg[i] <= 1'b0;
            end else begin
                if (i==0) begin
                    reset_reg[i] <= 1'b1;
                end else if (i < RESET_SYNC_STAGES) begin
                    reset_reg[i] <= reset_reg[i-1];
                end else begin
                    reset_reg[i] <= reset_reg[RESET_SYNC_STAGES-2];
                end
            end
        end
    end
endgenerate

assign reset_n_sync = reset_reg[RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:RESET_SYNC_STAGES-1];

endmodule