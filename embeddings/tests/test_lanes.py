from multiplicity_core.lanes import MultiClassLaneStore


def test_lane_store_per_class_isolated():
    store = MultiClassLaneStore(active_class="1A")
    store.write(5, 42)  # class 1A
    store.switch_class("2B")
    assert store.read(5, default=0) == 0
    store.write(5, 7)  # class 2B
    assert store.read(5) == 7
    # Switch back
    store.switch_class("1A")
    assert store.read(5) == 42
