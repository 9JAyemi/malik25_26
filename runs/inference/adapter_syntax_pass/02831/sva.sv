module flip_flop_sva #(
    parameter int type = 0
) (
    input logic clk,
    input logic rst,
    input logic data,
    input logic q,
    input logic q_bar
);

    // Reset drives the default output state for the selected flip-flop type.
    check_reset_state: assert property (
        @(posedge clk)
        rst |-> (q == ((type == 1) || (type == 3))) &&
                (q_bar == (!((type == 1) || (type == 3))))
    );

    // D-type flip-flops capture data on the next clock.
    generate
        if (type == 0) begin : gen_d_type
            check_d_type_capture: assert property (
                @(posedge clk) disable iff (rst)
                1'b1 |=> (q == $past(data)) &&
                         (q_bar == ~$past(data))
            );
        end
    endgenerate

    // JK flip-flops toggle q_bar when data is high.
    generate
        if (type == 1) begin : gen_jk_type
            check_jk_set_toggle: assert property (
                @(posedge clk) disable iff (rst)
                data |=> (q == ~$past(q_bar)) &&
                         (q_bar == ~$past(q))
            );
        end
    endgenerate

    // JK flip-flops hold both outputs when data is low.
    generate
        if (type == 1) begin : gen_jk_type
            check_jk_hold: assert property (
                @(posedge clk) disable iff (rst)
                !data |=> (q == $past(q)) &&
                          (q_bar == $past(q_bar))
            );
        end
    endgenerate

    // T flip-flops toggle q when data is high.
    generate
        if (type == 2) begin : gen_t_type
            check_t_type_toggle: assert property (
                @(posedge clk) disable iff (rst)
                data |=> (q == ~$past(q)) &&
                         (q_bar == $past(q_bar))
            );
        end
    endgenerate

    // T flip-flops hold both outputs when data is low.
    generate
        if (type == 2) begin : gen_t_type
            check_t_type_hold: assert property (
                @(posedge clk) disable iff (rst)
                !data |=> (q == $past(q)) &&
                          (q_bar == $past(q_bar))
            );
        end
    endgenerate

    // SR flip-flops set q when data is high.
    generate
        if (type == 3) begin : gen_sr_type
            check_sr_set_q: assert property (
                @(posedge clk) disable iff (rst)
                data |=> (q == 1'b1) &&
                         (q_bar == 1'b0)
            );
        end
    endgenerate

    // SR flip-flops hold both outputs when data is low.
    generate
        if (type == 3) begin : gen_sr_type
            check_sr_hold: assert property (
                @(posedge clk) disable iff (rst)
                !data |=> (q == $past(q)) &&
                          (q_bar == $past(q_bar))
            );
        end
    endgenerate

endmodule