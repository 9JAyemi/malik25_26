module four_input_mux_sva (
    input logic [3:0] data_in_0,
    input logic [3:0] data_in_1,
    input logic [3:0] data_in_2,
    input logic [3:0] data_in_3,
    input logic [1:0] select,
    input logic [3:0] data_out
);
    // Note: No clock or reset in RTL; combinational 4:1 mux. Assertions are sampled on edges of select and data inputs.

    // Mux selects data_in_0 when select==2'b00.
    check_sel_00: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) (select == 2'b00) |-> (data_out == data_in_0)
    );

    // Mux selects data_in_1 when select==2'b01.
    check_sel_01: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) (select == 2'b01) |-> (data_out == data_in_1)
    );

    // Mux selects data_in_2 when select==2'b10.
    check_sel_10: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) (select == 2'b10) |-> (data_out == data_in_2)
    );

    // Mux selects data_in_3 when select==2'b11.
    check_sel_11: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) (select == 2'b11) |-> (data_out == data_in_3)
    );

    // Mux function equivalence to conditional expression for all select values.
    check_mux_function_equiv: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) 1'b1 |-> (data_out == (select == 2'b00 ? data_in_0 :
                                 select == 2'b01 ? data_in_1 :
                                 select == 2'b10 ? data_in_2 : data_in_3))
    );

    // When selected, changes on data_in_0 must reflect on data_out.
    passthrough_0: assert property (
        @(posedge data_in_0[0] or negedge data_in_0[0] or
          posedge data_in_0[1] or negedge data_in_0[1] or
          posedge data_in_0[2] or negedge data_in_0[2] or
          posedge data_in_0[3] or negedge data_in_0[3]
        ) (select == 2'b00) |-> (data_out == data_in_0)
    );

    // When selected, changes on data_in_1 must reflect on data_out.
    passthrough_1: assert property (
        @(posedge data_in_1[0] or negedge data_in_1[0] or
          posedge data_in_1[1] or negedge data_in_1[1] or
          posedge data_in_1[2] or negedge data_in_1[2] or
          posedge data_in_1[3] or negedge data_in_1[3]
        ) (select == 2'b01) |-> (data_out == data_in_1)
    );

    // When selected, changes on data_in_2 must reflect on data_out.
    passthrough_2: assert property (
        @(posedge data_in_2[0] or negedge data_in_2[0] or
          posedge data_in_2[1] or negedge data_in_2[1] or
          posedge data_in_2[2] or negedge data_in_2[2] or
          posedge data_in_2[3] or negedge data_in_2[3]
        ) (select == 2'b10) |-> (data_out == data_in_2)
    );

    // When selected, changes on data_in_3 must reflect on data_out.
    passthrough_3: assert property (
        @(posedge data_in_3[0] or negedge data_in_3[0] or
          posedge data_in_3[1] or negedge data_in_3[1] or
          posedge data_in_3[2] or negedge data_in_3[2] or
          posedge data_in_3[3] or negedge data_in_3[3]
        ) (select == 2'b11) |-> (data_out == data_in_3)
    );

    // Output changes only if select changes or the currently selected input changes.
    check_output_change_cause: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1]
          or posedge data_in_0[0] or negedge data_in_0[0] or posedge data_in_0[1] or negedge data_in_0[1]
          or posedge data_in_0[2] or negedge data_in_0[2] or posedge data_in_0[3] or negedge data_in_0[3]
          or posedge data_in_1[0] or negedge data_in_1[0] or posedge data_in_1[1] or negedge data_in_1[1]
          or posedge data_in_1[2] or negedge data_in_1[2] or posedge data_in_1[3] or negedge data_in_1[3]
          or posedge data_in_2[0] or negedge data_in_2[0] or posedge data_in_2[1] or negedge data_in_2[1]
          or posedge data_in_2[2] or negedge data_in_2[2] or posedge data_in_2[3] or negedge data_in_2[3]
          or posedge data_in_3[0] or negedge data_in_3[0] or posedge data_in_3[1] or negedge data_in_3[1]
          or posedge data_in_3[2] or negedge data_in_3[2] or posedge data_in_3[3] or negedge data_in_3[3]
        ) $changed(data_out) |-> (
              $changed(select)
           || ((select == 2'b00) && $changed(data_in_0))
           || ((select == 2'b01) && $changed(data_in_1))
           || ((select == 2'b10) && $changed(data_in_2))
           || ((select == 2'b11) && $changed(data_in_3))
        )
    );

endmodule