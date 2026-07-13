module ThermoGauge_sva #(
    parameter int LOGWORD = 0
)(
    input logic clk,
    input logic [(1<<LOGWORD)-1:0] gauge,
    input logic [((LOGWORD > 0) ? LOGWORD : 1)-1:0] value,
    input logic enable,
    input logic enforce
);

    localparam int WORD  = (1 << LOGWORD);
    localparam int PAD_W = (LOGWORD > 0) ? (WORD - (LOGWORD + 1)) : 0;

    generate
        if (LOGWORD > 0) begin : gen_logword_gt_0

            // Gauge matches the RTL's muxed combinational result.
            check_gauge_matches_rtl_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                gauge == ((enable && !enforce) ?
                          ({{PAD_W{1'b0}}, 1'b0, value[LOGWORD-1:0]} + 1'b1) :
                          {{PAD_W{1'b0}}, 1'b0, value[LOGWORD-1:0]})
            );

            // Enforce selects the non-incremented value path.
            check_enforce_selects_base_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                enforce |-> (gauge == {{PAD_W{1'b0}}, 1'b0, value[LOGWORD-1:0]})
            );

            // Disable selects the non-incremented value path.
            check_disable_selects_base_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                (!enable) |-> (gauge == {{PAD_W{1'b0}}, 1'b0, value[LOGWORD-1:0]})
            );

            // Enable without enforce selects the incremented value path.
            check_enable_selects_increment_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                (enable && !enforce) |-> (gauge == ({{PAD_W{1'b0}}, 1'b0, value[LOGWORD-1:0]} + 1'b1))
            );

            // On the base path, the low bits mirror value.
            check_base_path_low_bits_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                ((!enable) || enforce) |-> (gauge[LOGWORD-1:0] == value[LOGWORD-1:0])
            );

            // On the base path, bit LOGWORD is forced low.
            check_base_path_inserted_zero_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                ((!enable) || enforce) |-> (gauge[LOGWORD] == 1'b0)
            );

            // Incrementing an all-ones value creates a carry into bit LOGWORD.
            check_increment_carry_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                (enable && !enforce && (&value[LOGWORD-1:0])) |->
                ((gauge[LOGWORD] == 1'b1) && (gauge[LOGWORD-1:0] == {LOGWORD{1'b0}}))
            );

            // Incrementing any other value does not set bit LOGWORD.
            check_increment_no_carry_nz: assert property (
                @(posedge clk) disable iff (1'b0)
                (enable && !enforce && !(|(~value[LOGWORD-1:0]))) && !(&value[LOGWORD-1:0]) |->
                (gauge[LOGWORD] == 1'b0)
            );

            if (WORD > (LOGWORD + 1)) begin : gen_upper_bits
                // Bits above LOGWORD remain zero.
                check_upper_bits_zero_nz: assert property (
                    @(posedge clk) disable iff (1'b0)
                    gauge[WORD-1:LOGWORD+1] == {(WORD-(LOGWORD+1)){1'b0}}
                );
            end

        end else begin : gen_logword_eq_0

            // With LOGWORD==0, gauge is high only when enable is high and enforce is low.
            check_gauge_matches_rtl_z0: assert property (
                @(posedge clk) disable iff (1'b0)
                gauge == (enable && !enforce)
            );

            // Enforce clears the one-bit output.
            check_enforce_clears_gauge_z0: assert property (
                @(posedge clk) disable iff (1'b0)
                enforce |-> (gauge == 1'b0)
            );

            // Disable clears the one-bit output.
            check_disable_clears_gauge_z0: assert property (
                @(posedge clk) disable iff (1'b0)
                (!enable) |-> (gauge == 1'b0)
            );

            // Enable without enforce sets the one-bit output.
            check_enable_sets_gauge_z0: assert property (
                @(posedge clk) disable iff (1'b0)
                (enable && !enforce) |-> (gauge == 1'b1)
            );

        end
    endgenerate

endmodule