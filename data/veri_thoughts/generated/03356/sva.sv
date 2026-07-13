module usb_controller_sva #(
    parameter int data_width = 8,
    parameter int addr_width = 8,
    parameter int ctrl_type  = 0
) (
    input logic clk,
    input logic rst,
    input logic usb_in,
    input logic [data_width-1:0] data_in,
    input logic [addr_width-1:0] addr_in,
    input logic usb_out,
    input logic [data_width-1:0] data_out,
    input logic [addr_width-1:0] addr_out,
    input logic tx_en,
    input logic tx_done,
    input logic rx_en,
    input logic rx_done
);

    localparam logic [data_width-1:0] USB_ONE = {{(data_width-1){1'b0}}, 1'b1};

    // Formal starts with reset asserted.
    assume_initial_reset: assume property (
        @(posedge clk) $initstate |-> rst
    );

    // Reset clears the registered outputs and drives usb_out low.
    reset_clears_registers: assert property (
        @(posedge clk) rst |=> (data_out == {data_width{1'b0}}) &&
                               (addr_out == {addr_width{1'b0}}) &&
                               (tx_en == 1'b0) &&
                               (rx_done == 1'b0) &&
                               (usb_out == 1'b0)
    );

    generate
        if (ctrl_type == 0) begin : gen_type0
            // RX is never active in TX-only mode.
            rx_done_never_asserts_t0: assert property (
                @(posedge clk) disable iff (rst) (rx_done == 1'b0)
            );

            // A TX start can only come from tx_done being high.
            tx_start_requires_tx_done_t0: assert property (
                @(posedge clk) disable iff (rst) $rose(tx_en) |-> $past(tx_done)
            );

            // A TX start captures the input data and address.
            tx_start_captures_inputs_t0: assert property (
                @(posedge clk) disable iff (rst) $rose(tx_en) |-> (data_out == $past(data_in)) &&
                                                                   (addr_out == $past(addr_in))
            );

            // data_out or addr_out only change when TX starts.
            tx_capture_changes_only_on_start_t0: assert property (
                @(posedge clk) disable iff (rst) ($changed(data_out) || $changed(addr_out)) |-> $rose(tx_en)
            );

            // In TX-only mode, usb_out follows the TX data LSB when enabled.
            usb_out_matches_tx_path_t0: assert property (
                @(posedge clk) disable iff (rst) usb_out == (tx_en ? data_out[0] : 1'b0)
            );

            // During an active TX without completion, outputs hold their values.
            tx_holds_outputs_until_done_t0: assert property (
                @(posedge clk) disable iff (rst) (tx_en && !tx_done) |=> tx_en &&
                                                                      $stable(data_out) &&
                                                                      $stable(addr_out)
            );

            // A completed TX drops tx_en on the next cycle.
            tx_done_clears_enable_t0: assert property (
                @(posedge clk) disable iff (rst) (tx_en && tx_done) |=> !tx_en
            );
        end else if (ctrl_type == 1) begin : gen_type1
            // A TX enable rise can only come from tx_done being high.
            tx_enable_rise_requires_tx_done_t1: assert property (
                @(posedge clk) disable iff (rst) $rose(tx_en) |-> $past(tx_done)
            );

            // A TX enable rise captures the input data and address.
            tx_enable_rise_captures_inputs_t1: assert property (
                @(posedge clk) disable iff (rst) $rose(tx_en) |-> (data_out == $past(data_in)) &&
                                                                  (addr_out == $past(addr_in))
            );

            // tx_en only falls after tx_done is seen.
            tx_enable_fall_requires_tx_done_t1: assert property (
                @(posedge clk) disable iff (rst) $fell(tx_en) |-> $past(tx_done)
            );

            // Without tx_done, tx_en stays asserted.
            tx_enable_holds_without_tx_done_t1: assert property (
                @(posedge clk) disable iff (rst) (tx_en && !tx_done) |=> tx_en
            );

            // An RX completion requires usb_in to have been high.
            rx_complete_requires_usb_in_t1: assert property (
                @(posedge clk) disable iff (rst) $rose(rx_done) |-> $past(usb_in)
            );

            // An RX completion captures 1 into data_out, the address, and leaves usb_out low.
            rx_complete_captures_and_drops_usb_t1: assert property (
                @(posedge clk) disable iff (rst) $rose(rx_done) |-> (data_out == USB_ONE) &&
                                                                  (addr_out == $past(addr_in)) &&
                                                                  (usb_out == 1'b0)
            );

            // rx_done only falls when a new RX is requested.
            rx_done_fall_requires_rx_en_t1: assert property (
                @(posedge clk) disable iff (rst) $fell(rx_done) |-> $past(rx_en)
            );

            // Without rx_en, rx_done remains asserted.
            rx_done_holds_without_rx_en_t1: assert property (
                @(posedge clk) disable iff (rst) (rx_done && !rx_en) |=> rx_done
            );

            // Data or address changes without RX completion require tx_done.
            tx_capture_update_requires_tx_done_t1: assert property (
                @(posedge clk) disable iff (rst) (($changed(data_out) || $changed(addr_out)) && !$rose(rx_done)) |-> $past(tx_done)
            );

            // usb_out high while usb_in is low can only happen with TX enabled.
            usb_out_high_without_usb_in_requires_tx_enable_t1: assert property (
                @(posedge clk) disable iff (rst) (usb_out && !usb_in) |-> tx_en
            );
        end else if (ctrl_type == 2) begin : gen_type2
            // TX is never active in RX-only mode.
            tx_en_never_asserts_t2: assert property (
                @(posedge clk) disable iff (rst) (tx_en == 1'b0)
            );

            // An RX completion requires usb_in to have been high.
            rx_complete_requires_usb_in_t2: assert property (
                @(posedge clk) disable iff (rst) $rose(rx_done) |-> $past(usb_in)
            );

            // An RX completion captures 1 into data_out, the address, and leaves usb_out low.
            rx_complete_captures_and_drops_usb_t2: assert property (
                @(posedge clk) disable iff (rst) $rose(rx_done) |-> (data_out == USB_ONE) &&
                                                                  (addr_out == $past(addr_in)) &&
                                                                  (usb_out == 1'b0)
            );

            // data_out or addr_out only change on RX completion.
            rx_capture_changes_only_on_complete_t2: assert property (
                @(posedge clk) disable iff (rst) ($changed(data_out) || $changed(addr_out)) |-> $rose(rx_done)
            );

            // rx_done only falls when a new RX is requested.
            rx_done_fall_requires_rx_en_t2: assert property (
                @(posedge clk) disable iff (rst) $fell(rx_done) |-> $past(rx_en)
            );

            // Without rx_en, rx_done remains asserted.
            rx_done_holds_without_rx_en_t2: assert property (
                @(posedge clk) disable iff (rst) (rx_done && !rx_en) |=> rx_done
            );

            // In RX-only mode, usb_out can only be high when usb_in is high.
            usb_out_high_requires_usb_in_t2: assert property (
                @(posedge clk) disable iff (rst) usb_out |-> usb_in
            );
        end else begin : gen_other
            // Unsupported type never enables TX.
            tx_en_never_asserts_other: assert property (
                @(posedge clk) disable iff (rst) (tx_en == 1'b0)
            );

            // Unsupported type never completes RX.
            rx_done_never_asserts_other: assert property (
                @(posedge clk) disable iff (rst) (rx_done == 1'b0)
            );

            // Unsupported type keeps usb_out low.
            usb_out_stays_low_other: assert property (
                @(posedge clk) disable iff (rst) (usb_out == 1'b0)
            );

            // Unsupported type leaves data and address cleared.
            outputs_stay_cleared_other: assert property (
                @(posedge clk) disable iff (rst) (data_out == {data_width{1'b0}}) &&
                                              (addr_out == {addr_width{1'b0}})
            );
        end
    endgenerate

endmodule