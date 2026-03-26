module and_or_array_sva
#(
    parameter int width = 8,
    parameter int sel = 1
)
(
    input logic clk,
    input logic [width-1:0] a,
    input logic y
);

generate
    if (width > 1) begin : gen_valid_width
        if (sel == 1) begin : gen_and_mode
            // y matches the reduction AND of a.
            check_and_reduction: assert property (
                @(posedge clk) y == (&a)
            );

            // All input bits high drives y high.
            check_and_all_ones_drive_high: assert property (
                @(posedge clk) (&a) |-> y
            );

            // Any low input bit forces y low.
            check_and_any_zero_forces_low: assert property (
                @(posedge clk) !(&a) |-> !y
            );
        end
        else begin : gen_or_mode
            // y matches the reduction OR of a.
            check_or_reduction: assert property (
                @(posedge clk) y == (|a)
            );

            // Any high input bit forces y high.
            check_or_any_one_forces_high: assert property (
                @(posedge clk) (|a) |-> y
            );

            // All input bits low drives y low.
            check_or_all_zeros_drive_low: assert property (
                @(posedge clk) !(|a) |-> !y
            );
        end
    end
endgenerate

endmodule