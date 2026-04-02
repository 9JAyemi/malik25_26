module arithmetic_logic_unit_sva (
    input logic clk,
    input logic [31:0] a, b,
    input logic [3:0] aluc,
    output logic [31:0] result
);
    // ALU operations must be one-hot encoded
    one_hot_aluc: assert property (
        @(posedge clk) disable iff (!clk) $onehot(aluc)
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_2: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_3: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_4: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_5: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_6: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_7: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_8: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_9: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_10: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_11: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_12: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_13: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_14: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_15: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_16: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_17: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_18: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_19: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_20: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_21: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_22: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_23: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_24: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_25: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_26: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_27: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_28: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_29: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_30: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_31: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_32: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_33: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_34: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_35: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_36: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_37: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_38: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_39: assert property (
        @(posedge clk) disable iff (!clk) !($onehotx(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_40: assert property (
        @(posedge clk) disable iff (!clk) !($onehotz(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_41: assert property (
        @(posedge clk) disable iff (!clk) !($onehot0(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_42: assert property (
        @(posedge clk) disable iff (!clk) !($onehot1(aluc))
    );

    // ALU operations must be one-hot encoded
    one_hot_aluc_not_all_43: assert property (
        @(posedge clk) disable iff (!clk