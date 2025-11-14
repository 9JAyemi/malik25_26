

module altera_tse_reset_synchronizer
#(
    parameter ASYNC_RESET = 1,
    parameter DEPTH       = 2
)
(
    input   reset_in ,

    input   clk,
    output  reset_out
);

     reg [DEPTH-1:0] altera_tse_reset_synchronizer_chain;
    reg altera_tse_reset_synchronizer_chain_out;

    generate if (ASYNC_RESET) begin

        always @(posedge clk or posedge reset_in) begin
            if (reset_in) begin
                altera_tse_reset_synchronizer_chain <= {DEPTH{1'b1}};
                altera_tse_reset_synchronizer_chain_out <= 1'b1;
            end
            else begin
                altera_tse_reset_synchronizer_chain[DEPTH-2:0] <= altera_tse_reset_synchronizer_chain[DEPTH-1:1];
                altera_tse_reset_synchronizer_chain[DEPTH-1] <= 0;
                altera_tse_reset_synchronizer_chain_out <= altera_tse_reset_synchronizer_chain[0];
            end
        end

        assign reset_out = altera_tse_reset_synchronizer_chain_out;
     
    end else begin

        always @(posedge clk) begin
            altera_tse_reset_synchronizer_chain[DEPTH-2:0] <= altera_tse_reset_synchronizer_chain[DEPTH-1:1];
            altera_tse_reset_synchronizer_chain[DEPTH-1] <= reset_in;
            altera_tse_reset_synchronizer_chain_out <= altera_tse_reset_synchronizer_chain[0];
        end

        assign reset_out = altera_tse_reset_synchronizer_chain_out;
 
    end
    endgenerate

endmodule
