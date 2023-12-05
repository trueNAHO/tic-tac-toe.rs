use educe::Educe;

/// A [`Player`].
#[derive(Educe)]
#[educe(Default)]
pub struct Player {
    #[educe(Default(expression = "String::new()"))]
    pub mark: String,

    #[educe(Default(expression = "String::new()"))]
    pub name: String,
}
